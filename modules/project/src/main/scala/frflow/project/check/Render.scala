package frflow.project.check

import cats.{Monad, Parallel}
import cats.syntax.all.*
import frflow.core.name.{KbName, RelPath}
import frflow.project.pipeline.{Analysis, LeanSources}
import frflow.project.port.ProjectFiles
import frflow.proof.lean.ast.ModuleName
import frflow.proof.lean.print.Print

/** The project's Lean workspace written: `lean/lakefile.toml` (FrFlow's generated library and the developer's proofs,
  * requiring FrFlow's Lean library at `library`, relative to `lean/`), `lean/lean-toolchain`, each generated module
  * whose text changed, and no generated module the model no longer has.
  */
final class Render[F[_]: Monad: Parallel](files: ProjectFiles[F], library: String):
  /** The modules written. */
  def apply(a: Analysis): F[List[ModuleName]] =
    val kb = a.decided.theory.name
    val generated = a.modules.map(_.name.file).toSet
    for
      _       <- files.writeIfChanged(Render.lakefile, Render.lakefileOf(kb, library))
      _       <- files.writeIfChanged(Render.toolchain, LeanSources.Toolchain)
      written <- a.modules.parTraverseFilter(m =>
                   files.writeIfChanged(m.name.file, Print.module(m)).map(Option.when(_)(m.name)))
      stale   <- files.list(RelPath.fromIdentifiers("lean", s"FrFlowGen/${kb.value}")).map(_.filterNot(generated))
      _       <- stale.traverse_(files.delete)
    yield written

object Render:
  val lakefile: RelPath = RelPath.fromIdentifiers("lean", "lakefile.toml")
  val toolchain: RelPath = RelPath.fromIdentifiers("lean", "lean-toolchain")

  def lakefileOf(kb: KbName, library: String): String =
    s"""name = "${kb.value.toLowerCase}"
       |defaultTargets = ["FrFlowGen"]
       |
       |[[require]]
       |name = "frflow"
       |path = "${library.replace("\\", "/")}"
       |
       |[[lean_lib]]
       |name = "FrFlowGen"
       |globs = ["FrFlowGen.+"]
       |
       |[[lean_lib]]
       |name = "Proofs"
       |globs = ["Proofs.+"]
       |""".stripMargin

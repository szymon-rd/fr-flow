package frflow.project.check

import cats.{Monad, Parallel}
import cats.syntax.all.*
import frflow.core.name.RelPath
import frflow.project.pipeline.Analysis
import frflow.project.port.ProjectFiles
import frflow.proof.lean.ast.ModuleName
import frflow.proof.rocq.RocqProject

/** The project's Rocq written: `rocq/_CoqProject` (where an editor finds what a check compiled), each generated
  * module whose text changed, and no generated module the model no longer has.
  */
final class Render[F[_]: Monad: Parallel](files: ProjectFiles[F]):
  /** The modules written. */
  def apply(a: Analysis): F[List[ModuleName]] =
    val printed = a.modules.flatMap(m => a.rocq.text(m.name).map(m.name -> _))
    val generated = printed.map((name, _) => RocqProject.path(name)).toSet
    for
      _       <- files.writeIfChanged(Render.project, Render.Project)
      written <- printed.parTraverseFilter((name, text) =>
                   files.writeIfChanged(RocqProject.path(name), text).map(Option.when(_)(name)))
      stale   <- files.list(RelPath.fromIdentifiers("rocq", s"FrFlowGen/${a.decided.theory.name.value}"))
                   .map(_.filterNot(generated))
      _       <- stale.traverse_(files.delete)
    yield written

object Render:
  val project: RelPath = RelPath.fromIdentifiers("rocq", "_CoqProject")

  /** What a check compiles is under `rocq/_build/`, by the name Rocq loads each module by. */
  val Project: String =
    List("FrFlow", "FrFlowGen", "Proofs").map(root => s"-Q _build/$root $root\n").mkString

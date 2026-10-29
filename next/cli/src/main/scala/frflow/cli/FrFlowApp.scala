package frflow.cli

import cats.data.NonEmptyChain
import cats.effect.{ExitCode, IO, IOApp}
import cats.syntax.all.*
import frflow.api.{Extension, FrFlowProject, Project}
import frflow.core.name.RelPath
import frflow.dsl.build.ElabError
import frflow.dsl.example.FrFlowExamples
import frflow.dsl.kb.FrModel
import java.nio.file.Path

/** The command line of a FrModel, which a project's main object extends: the composition root, where the project is
  * put together and `IO` chosen.
  * {{{
  * object roomsCli extends frflow.cli.FrFlowApp(rooms, root = "examples/rooms")
  * }}}
  * `root` is the project's directory (`FRFLOW_ROOT` overrides it); `extensions`, the layers on top it uses (their
  * commands follow FrFlow's). The plain Scala of its models' operations, tested against them, is the FrModel's
  * (`implementTested(ops*)(start, observe)(calls)`), its effect `IO`. Its examples are
  * the `FrFlowExamples` classes among its test classes (`frflow.tests`), and those `examples` names. Override
  * `sources` (directories relative to the project) and `library` (FrFlow's Lean library, relative to its `lean/`)
  * where the project keeps them elsewhere. A usage error prints the help and exits 2. The web view runs from the same
  * object, through sbt (`sbt "PROJECT/serve --as NAME"`).
  */
abstract class FrFlowApp(model: => FrModel, root: String = ".", val extensions: List[Extension] = Nil)
    extends IOApp with FrFlowProject:
  def sources: List[String] = List("src/main")
  def library: String = FrFlowApp.Library
  def examples: List[FrFlowExamples] = Nil

  private lazy val kb: FrModel = model

  final def directory(env: Map[String, String]): Path =
    Path.of(env.getOrElse("FRFLOW_ROOT", root)).toAbsolutePath.normalize

  /** The model elaborated, with its own examples (those found written for another model are left out). */
  final def project: IO[Either[NonEmptyChain[ElabError], Project]] =
    TestClasses.examples(sys.props.get("frflow.tests")).map { found =>
      val written = (examples ++ found.filter(_.knowledge eq kb)).distinctBy(_.getClass)
      (kb.elaborated, written.traverse(_.elaborated).map(_.flatten)).mapN((e, xs) =>
        Project(e, xs, sources.flatMap(RelPath.parse(_).toOption), Path.of(library))).toEither
    }

  final def run(args: List[String]): IO[ExitCode] = Launch(this, args)

object FrFlowApp:
  /** FrFlow's Lean library (`next/proof/lean`) from a project's `lean/` under `examples/NAME`, as `init` makes it. */
  val Library: String = "../../../next/proof/lean"

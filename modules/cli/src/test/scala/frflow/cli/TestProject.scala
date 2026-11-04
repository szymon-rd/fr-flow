package frflow.cli

import cats.data.NonEmptyChain
import cats.effect.IO
import frflow.api.{Extension, FrFlowProject, Project}
import frflow.dsl.build.ElabError
import java.nio.file.Path

/** A project's main object as `Launch` sees it, at `dir`, with nothing to open. */
final case class TestProject(dir: Path, env: Map[String, String]) extends FrFlowProject:
  def project: IO[Either[NonEmptyChain[ElabError], Project]] =
    IO.raiseError(AssertionError("not opened"))
  def directory(env: Map[String, String]): Path = dir
  def extensions: List[Extension] = Nil

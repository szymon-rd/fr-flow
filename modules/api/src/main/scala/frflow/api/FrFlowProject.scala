package frflow.api

import cats.data.NonEmptyChain
import cats.effect.IO
import frflow.dsl.build.ElabError
import java.nio.file.Path

/** What a project's main object gives the front ends (the command line's `FrFlowApp`, the web view's `serve`): the
  * project, or what keeps its model or its examples from elaborating (its examples' classes are read from where the
  * build put them, hence `IO`); its directory, as the environment gives it; and the layers on top it uses.
  */
trait FrFlowProject:
  def project: IO[Either[NonEmptyChain[ElabError], Project]]
  def directory(env: Map[String, String]): Path
  def extensions: List[Extension]

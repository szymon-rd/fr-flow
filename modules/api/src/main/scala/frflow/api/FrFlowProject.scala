package frflow.api

import cats.effect.IO
import java.nio.file.Path

/** A project as its front ends open it: the FrModel, its directory (`FRFLOW_ROOT` overrides it), FrFlow's Lean
  * kernel relative to its `lean/`, and the layers on top it uses. A project's main object is one (the CLI's `FrFlowApp`);
  * the web view's `serve` task opens the same object.
  */
trait FrFlowProject:
  def kb: frflow.FrModel
  def root: String
  def kernelPath: String
  def extensions: List[Extension] = Nil
  def directory(env: Map[String, String]): Path = Path.of(env.getOrElse("FRFLOW_ROOT", root)).toAbsolutePath.normalize
  def api(env: Map[String, String]): IO[FrFlowApi] = LiveApi.fromEnv(kb, root, kernelPath, env)
  def host(env: Map[String, String]): IO[Host] = api(env).map(Host(_, directory(env), env))

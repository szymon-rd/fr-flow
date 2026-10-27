package frflow.api

import frflow.decision.rules.Refusal
import java.nio.file.Path

/** A project open in a front end, as a layer on top sees it: reading it, and who the developer is (`as`, else
  * `FRFLOW_AS`, else the name their key is listed under); never deciding or proving, which stay the front end's own
  * commands. Its directory is where a layer keeps its own files; `env`, the environment it runs in.
  */
final case class Host[F[_]](reading: Reading[F], developer: Option[String] => F[Either[Refusal, String]],
    directory: Path, env: Map[String, String])

object Host:
  /** What of `api` a layer on top may use. */
  def of[F[_]](api: FrFlowApi[F], directory: Path, env: Map[String, String]): Host[F] =
    Host(api.reading, api.deciding.developer, directory, env)

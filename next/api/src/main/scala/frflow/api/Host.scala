package frflow.api

import java.nio.file.Path

/** A project open in a front end, as a layer on top sees it: the API over it, its directory (where a layer keeps its
  * own files), and the environment it runs in.
  */
final case class Host[F[_]](api: FrFlowApi[F], directory: Path, env: Map[String, String])

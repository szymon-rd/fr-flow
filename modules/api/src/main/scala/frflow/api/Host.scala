package frflow.api

import java.nio.file.Path

/** What a layer on top works with: the project's API, its directory (where it keeps its own files, under `.frflow/`),
  * and the environment.
  */
final case class Host(api: FrFlowApi, directory: Path, env: Map[String, String])

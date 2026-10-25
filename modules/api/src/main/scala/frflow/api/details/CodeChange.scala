package frflow.api
package details

import io.circe.Codec

/** How the code a node governs changed since it was decided (a git diff), or, never decided, the files in full. */
final case class CodeChange(files: List[String], text: String, inFull: Boolean) derives Codec.AsObject

package frflow.wire.file

import io.circe.{Decoder, Encoder}

/** One of FrFlow's files: its path under the project, the version this FrFlow writes and reads, and its body's
  * codec (an object, which `Files` writes after the version); and how each earlier version it still reads is read
  * (`older`), into what this version holds.
  */
final case class FileFormat[A](file: String, version: Int, encoder: Encoder.AsObject[A], decoder: Decoder[A],
    older: Map[Int, Decoder[A]] = Map.empty[Int, Decoder[A]])

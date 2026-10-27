package frflow.wire.file

import io.circe.{Decoder, DecodingFailure, HCursor, Json}

/** A case of an enum with fields, written as an object: `kind` first (the case's word), then its fields. */
object Tagged:
  def apply(kind: String, fields: (String, Json)*): Json =
    Json.fromFields(("kind" -> Json.fromString(kind)) +: fields)

  /** Read by its `kind`; an unknown kind fails at `kind`, naming what was read. */
  def decoder[A](what: String)(cases: PartialFunction[String, HCursor => Decoder.Result[A]]): Decoder[A] =
    Decoder.instance(c => c.get[String]("kind").flatMap(k =>
      cases.lift(k).fold(Left(DecodingFailure(s"no $what of kind $k", c.downField("kind").history)))(_(c))))

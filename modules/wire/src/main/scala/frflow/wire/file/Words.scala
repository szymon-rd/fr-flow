package frflow.wire.file

import io.circe.{Codec, Decoder, Encoder}

/** An enum whose cases have no fields, each written as its word, spelled at the codec so a rename in the domain does
  * not move a file.
  */
object Words:
  def codec[A](what: String, all: Iterable[A])(word: A => String): Codec[A] =
    val byWord = all.map(a => word(a) -> a).toMap
    Codec.from(Decoder.decodeString.emap(w => byWord.get(w).toRight(s"no $what $w")),
      Encoder.encodeString.contramap(word))

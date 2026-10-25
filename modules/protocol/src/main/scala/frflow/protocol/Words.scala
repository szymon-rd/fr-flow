package frflow.protocol

import io.circe.{Codec, Decoder, Encoder}

/** An enum written as a word (its `toString`): how statuses are stored and printed. */
trait Words[E]:
  def values: Array[E]
  private lazy val byWord = values.map(e => e.toString -> e).toMap
  given Codec[E] = Codec.from(Decoder.decodeString.emap(w => byWord.get(w).toRight(s"unknown value: $w")), Encoder.encodeString.contramap(_.toString))

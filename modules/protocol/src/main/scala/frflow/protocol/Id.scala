package frflow.protocol

import io.circe.{Codec, Decoder, Encoder, KeyDecoder, KeyEncoder}

/** Identifiers and hashes: strings on the wire, apart in the types. */
private[protocol] trait Id[T](using ev: T =:= String, back: String =:= T):
  def apply(s: String): T = back(s)
  extension (t: T) def value: String = ev(t)
  given Codec[T] = Codec.from(Decoder.decodeString.map(back(_)), Encoder.encodeString.contramap(ev(_)))
  given KeyEncoder[T] = KeyEncoder.encodeKeyString.contramap(ev(_))
  given KeyDecoder[T] = KeyDecoder.decodeKeyString.map(back(_))
  given Ordering[T] = Ordering.String.on(ev(_))

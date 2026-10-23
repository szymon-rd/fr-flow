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

/** A node's name in the model. */
opaque type NodeId = String
object NodeId extends Id[NodeId]

/** A SHA-256 in hex: of a node's content, or of what its check depends on. */
opaque type Hash = String
object Hash extends Id[Hash]

/** What a node rests on, hashed: the meaning of everything above it. "" for nothing. */
opaque type Chain = String
object Chain extends Id[Chain]:
  val empty: Chain = ""

/** The hash of the source files a node governs. */
opaque type Fingerprint = String
object Fingerprint extends Id[Fingerprint]

/** A developer key's id: the first 16 hex digits of its public key's hash. */
opaque type KeyId = String
object KeyId extends Id[KeyId]

/** A short reference to one decision (see `Ledger.entry`). */
opaque type EntryRef = String
object EntryRef extends Id[EntryRef]

/** A request of the developer's, in `.frflow/requests.json`. */
opaque type RequestId = String
object RequestId extends Id[RequestId]

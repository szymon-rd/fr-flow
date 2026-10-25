package frflow.protocol

/** What a node rests on, hashed: the meaning of everything above it. "" for nothing. */
opaque type Chain = String

object Chain extends Id[Chain]:
  val empty: Chain = ""

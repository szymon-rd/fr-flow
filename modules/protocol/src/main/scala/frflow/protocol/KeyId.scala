package frflow.protocol

/** A developer key's id: the first 16 hex digits of its public key's hash. */
opaque type KeyId = String

object KeyId extends Id[KeyId]

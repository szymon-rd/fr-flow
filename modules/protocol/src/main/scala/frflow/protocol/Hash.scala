package frflow.protocol

/** A SHA-256 in hex: of a node's content, or of what its check depends on. */
opaque type Hash = String

object Hash extends Id[Hash]

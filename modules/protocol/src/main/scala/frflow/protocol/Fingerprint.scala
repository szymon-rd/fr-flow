package frflow.protocol

/** The hash of the source files a node governs. */
opaque type Fingerprint = String

object Fingerprint extends Id[Fingerprint]

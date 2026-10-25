package frflow.protocol

/** A node as the developer last saw it (see the ledger's `Reading.version`): a decision sent with one is refused if it moved. */
opaque type Version = String

object Version extends Id[Version]

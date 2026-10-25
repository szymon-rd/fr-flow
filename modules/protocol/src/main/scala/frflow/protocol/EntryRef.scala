package frflow.protocol

/** A short reference to one decision (see `Ledger.entry`). */
opaque type EntryRef = String

object EntryRef extends Id[EntryRef]

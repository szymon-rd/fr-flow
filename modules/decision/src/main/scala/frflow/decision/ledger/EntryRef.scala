package frflow.decision.ledger

/** A decision's short reference: what a later decision of the same node names as the one it follows. */
opaque type EntryRef = String

object EntryRef:
  def apply(s: String): EntryRef = s
  extension (r: EntryRef) def value: String = r

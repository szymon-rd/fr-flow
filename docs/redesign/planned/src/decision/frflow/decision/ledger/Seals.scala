package frflow.decision.ledger

import frflow.core.name.NodeId

/** Signing decisions, pure once the key is read: `sign` the decisions a ledger has that the one before had not (their
  * `after` already set by `Ledger.add`). Whether one counts is `ledger.Deciders.counts`.
  */
object Seals:
  type Signer = Array[Byte] => Seal
  type Verifier = (Seal, Array[Byte]) => Boolean

  def signAdded(before: Ledger, after: Ledger, sign: Signer): Ledger =
    Ledger(after.decisions.map((id, ds) => id -> ds.zipWithIndex.map((d, i) =>
      if i < before.history(id).size then d else d.copy(seal = Some(sign(Payload.of(id, d)))))))


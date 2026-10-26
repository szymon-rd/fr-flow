package frflow.decision.ledger

import frflow.core.name.NodeId

/** Signing and verifying decisions, pure once the keys are read: `sign` the decisions a ledger has that the one before
  * had not (their `after` already set by `Ledger.add`), `verify` one against the filed public keys.
  */
object Seals:
  type Signer = Array[Byte] => Seal
  type Verifier = (Seal, Array[Byte]) => Boolean

  def signAdded(before: Ledger, after: Ledger, sign: Signer): Ledger =
    Ledger(after.decisions.map((id, ds) => id -> ds.zipWithIndex.map((d, i) =>
      if i < before.history(id).size then d else d.copy(seal = Some(sign(Payload.of(id, d)))))))

  def verify(check: Verifier)(id: NodeId, d: Decision): Boolean = d.seal.exists(s => check(s, Payload.of(id, d)))

package frflow.decision.ledger

import frflow.core.name.NodeId

/** What a signature covers: the node and everything its decision says (the rejected ids after their count), each
  * field framed (`Framed`). The new ledgers' own: no older signature is verified (the examples' ledgers start fresh).
  */
object Payload:
  def of(id: NodeId, d: Decision): Array[Byte] =
    Framed(List(id.value, d.action.toString.toLowerCase, d.author.by, d.author.at.toString, d.reason.text,
      d.reason.rejected.size.toString) ++ d.reason.rejected.map(_.value) ++ List(d.bound.chain.value,
      d.bound.code.fold("")(_.sha), d.author.commit.getOrElse(""), d.after.fold("")(_.value), d.bound.content.ref))

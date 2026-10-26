package frflow.decision.ledger

import frflow.core.name.NodeId
import java.nio.charset.StandardCharsets.UTF_8

/** What a signature covers: the node and everything its decision says, joined by NUL, as today's `Signing.payload`
  * (a golden test pins it on the examples' ledgers, so every recorded signature still verifies).
  */
object Payload:
  def of(id: NodeId, d: Decision): Array[Byte] =
    List(id.value, d.action.toString.toLowerCase, d.author.by, d.author.at.toString, d.reason.text,
      d.reason.rejected.map(_.value).mkString(","), d.bound.chain.value, d.bound.code.fold("")(_.stored),
      d.author.commit.getOrElse(""), d.after.fold("")(_.value), d.bound.content.ref).mkString("\u0000").getBytes(UTF_8)

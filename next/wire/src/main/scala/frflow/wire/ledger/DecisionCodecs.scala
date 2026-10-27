package frflow.wire.ledger

import cats.syntax.all.*
import frflow.core.name.NodeId
import frflow.decision.content.{Chain, CodeFingerprint, Content}
import frflow.decision.ledger.{Action, Authorship, Bound, Decision, EntryRef, Reason}
import frflow.wire.file.Names.given
import frflow.wire.file.Words
import io.circe.syntax.*
import io.circe.{Codec, Decoder, DecodingFailure, Json}
import java.time.Instant

/** A decision as the ledger writes it: what it does, who took it, when and at which commit, why, the content it is
  * bound to (by its `ref`, the content written once in the ledger's `contents`), the chain and code it is bound to,
  * the decision it follows, and its seal.
  */
object DecisionCodecs:
  given Codec[Action] = Words.codec("action", Action.values) {
    case Action.Accept  => "accept"
    case Action.Confirm => "confirm"
    case Action.Reject  => "reject"
    case Action.Revisit => "revisit"
    case Action.Remove  => "remove"
  }

  def encode(d: Decision): Json = Json.obj(
    "action" -> d.action.asJson, "by" -> d.author.by.asJson, "at" -> d.author.at.asJson,
    "commit" -> d.author.commit.asJson, "reason" -> d.reason.text.asJson, "rejected" -> d.reason.rejected.asJson,
    "content" -> d.bound.content.ref.asJson, "chain" -> d.bound.chain.value.asJson,
    "code" -> d.bound.code.map(_.sha).asJson, "after" -> d.after.map(_.value).asJson,
    "seal" -> d.seal.map(SealCodecs.encode).asJson)

  /** Read against the ledger's contents: a decision naming a content they do not hold does not read. */
  def decoder(contents: Map[String, Content]): Decoder[Decision] = Decoder.instance(c =>
    for
      action  <- c.get[Action]("action")
      author  <- (c.get[String]("by"), c.get[Instant]("at"), c.get[Option[String]]("commit")).mapN(Authorship(_, _, _))
      reason  <- (c.get[String]("reason"), c.get[List[NodeId]]("rejected")).mapN(Reason(_, _))
      ref     <- c.get[String]("content")
      content <- contents.get(ref).toRight(DecodingFailure(s"no content $ref in the ledger's contents",
                   c.downField("content").history))
      chain   <- c.get[String]("chain")
      code    <- c.get[Option[String]]("code")
      after   <- c.get[Option[String]]("after")
    yield Decision(action, author, reason, Bound(content, Chain(chain), code.map(CodeFingerprint(_))),
      after.map(EntryRef(_)), SealCodecs.optional(c.downField("seal"))))

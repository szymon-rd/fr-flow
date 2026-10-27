package frflow.wire.sample

import frflow.decision.content.{Chain, CodeFingerprint, Content, FieldValue}
import frflow.decision.ledger.{Action, Authorship, Bound, Decider, Deciders, Decision, EntryRef, Ledger, LedgerBase,
  Reason, Seal}
import frflow.wire.sample.Draws.*
import org.scalacheck.Gen

/** Ledgers and deciders' lists, every field drawn, optional ones present and absent. */
object LedgerDraws:
  val field: Gen[FieldValue] = Gen.oneOf(text.map(FieldValue.Text(_)), few(text).map(FieldValue.Texts(_)),
    few(Gen.zip(word, text)).map(fs => FieldValue.Record(fs.distinctBy(_._1))))

  /** Field names are distinct, as `Contents.of` makes them. */
  val content: Gen[Content] = few(Gen.zip(Gen.oneOf("kind", "statement", "formula", "parts", "sources", "Ü"), field))
    .map(fs => Content(fs.distinctBy(_._1)))

  val seal: Gen[Seal] = Gen.zip(hex, text).map(Seal(_, _))

  val decision: Gen[Decision] =
    for
      action  <- Gen.oneOf(Action.values.toList)
      author  <- Gen.zip(text, instant, Gen.option(hex)).map(Authorship(_, _, _))
      reason  <- Gen.zip(text, few(node)).map(Reason(_, _))
      bound   <- Gen.zip(content, Gen.oneOf(Gen.const(""), hex), Gen.option(hex.map(CodeFingerprint(_))))
                   .map((c, chain, code) => Bound(c, Chain(chain), code))
      after   <- Gen.option(hex.map(EntryRef(_)))
      signed  <- Gen.option(seal)
    yield Decision(action, author, reason, bound, after, signed)

  val ledger: Gen[Ledger] = byKey(node, few(decision)).map(Ledger(_))

  val decider: Gen[Decider] = Gen.zip(text, hex, text).map(Decider(_, _, _))
  val deciders: Gen[Deciders] = Gen.zip(few(decider), Gen.option(hex), Gen.option(seal)).map(Deciders(_, _, _))
  val base: Gen[LedgerBase] = Gen.zip(hex, Gen.option(hex), Gen.option(seal)).map(LedgerBase(_, _, _))

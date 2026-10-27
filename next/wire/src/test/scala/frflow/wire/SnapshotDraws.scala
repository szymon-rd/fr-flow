package frflow.wire

import frflow.wire.Draws.*
import frflow.wire.snapshot.*
import org.scalacheck.{Arbitrary, Gen}

/** Snapshots: nodes of both bodies, every row drawn. */
object SnapshotDraws:
  private val texts = few(text)
  private val field: Gen[FieldRow] = Gen.oneOf(text.map(FieldRow.Text(_)), texts.map(FieldRow.Texts(_)),
    few(Gen.zip(word, text)).map(fs => FieldRow.Record(fs.distinctBy(_._1))))

  val header: Gen[Header] = Gen.zip(text, text, hex, few(Gen.zip(word, field)).map(_.distinctBy(_._1)))
    .map(Header(_, _, _, _))
  val place: Gen[PlaceRow] = Gen.zip(texts, texts, texts, texts, texts).map(PlaceRow(_, _, _, _, _))
  val check: Gen[CheckRow] =
    Gen.zip(text, text, few(Gen.zip(text, text, text).map(ObligationRow(_, _, _)))).map(CheckRow(_, _, _))
  val test: Gen[TestRow] = Gen.zip(Gen.choose(0, 500), Arbitrary.arbitrary[Long], text, Gen.oneOf(true, false))
    .map(TestRow(_, _, _, _))
  val body: Gen[Body] = Gen.oneOf(texts.map(Body.Design(_)), Gen.zip(texts, Gen.option(text),
    Gen.option(Gen.zip(texts, texts, texts).map(CodeRow(_, _, _))), Gen.option(test)).map(Body.Stated(_, _, _, _)))

  val node: Gen[SnapNode] = Gen.zip(header, place, check, body).map(SnapNode(_, _, _, _))

  val snapshot: Gen[Snapshot] = Gen.zip(text, texts, texts, few(Gen.zip(text, text).map(TermRow(_, _))), few(node),
    few(Gen.zip(texts, texts, texts, texts, text).map(GroupRow(_, _, _, _, _))),
    few(Gen.zip(text, text, text).map(ExampleRow(_, _, _)))).map(Snapshot(_, _, _, _, _, _, _))

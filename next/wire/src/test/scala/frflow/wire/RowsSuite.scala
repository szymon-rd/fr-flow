package frflow.wire

import frflow.core.expr.{Side, Value}
import frflow.core.name.{CtorName, ModelName, NodeId}
import frflow.decision.content.{Content, FieldValue}
import frflow.eval.EvalError
import frflow.eval.run.Broken
import frflow.proof.obligation.{ObligationName, TryKind}
import frflow.proof.verdict.{ObligationStatus, Result}
import frflow.testing.Seed
import frflow.testing.report.{Against, Count, Outcome, TestReport}
import frflow.wire.snapshot.{FieldRow, ObligationRow, Rows, TestRow}

/** The one mapping from the domain to the snapshot's rows writes each value as the export says. */
class RowsSuite extends munit.FunSuite:
  test("a content's fields keep their order and their shape") {
    val c = Content(List("statement" -> FieldValue.Text("s"), "parts" -> FieldValue.Texts(List("A")),
      "sources" -> FieldValue.Record(List("store" -> "Store.scala"))))
    assertEquals(Rows.content(c), List("statement" -> FieldRow.Text("s"), "parts" -> FieldRow.Texts(List("A")),
      "sources" -> FieldRow.Record(List("store" -> "Store.scala"))))
  }

  test("a value is shown as an example shows it") {
    val oak = Value.Data(CtorName("Room"), List(Value.Str("Oak"), Value.Num(4)))
    assertEquals(Rows.shown(Value.Many(List(oak, Value.Maybe(None)))), "List(Room(\"Oak\", 4), None)")
    assertEquals(Rows.shown(Value.Pairs(List(Value.Num(1) -> Value.Inject(Side.Error, Value.Unit)))),
      "Map(1 -> Left(()))")
    assertEquals(Rows.shown(Value.World(List(ModelName("stored") -> Value.Bool(true)), List(false))),
      "World(stored: true; faults List(false))")
  }

  test("a test report becomes its row: cases, seed, what was tested, whether one failed") {
    val report = TestReport(Count(500, 500), Seed(42), Against.Model(NodeId("Store"), ModelName("stored")),
      Outcome.Passed, Nil, Nil)
    assertEquals(Rows.test(report), TestRow(500, "42", "model Store of stored", false))
  }

  test("an obligation is named as Lean names it, with its status as written today") {
    val r = Result(ObligationName.Tried(TryKind.Needed(NodeId("Free"))), ObligationStatus.NotShown, Nil)
    assertEquals(Rows.obligation(r, "theorem needed_Free : …"),
      ObligationRow("needed_Free", "not-shown", "theorem needed_Free : …"))
  }

  test("what a call broke is said in words") {
    assertEquals(Rows.broken(Broken.Always(NodeId("NoOverlap"))), "always NoOverlap")
    assertEquals(Rows.broken(Broken.NotEvaluated(EvalError.Quantified)), "not evaluated: it quantifies")
  }

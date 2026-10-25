package frflow
package check

import cats.effect.IO
import cats.effect.unsafe.implicits.global
import frflow.fixtures.*
import frflow.protocol.*

/** Contracts of one and three inputs, a flow of two and an invariant kept by a contract of three: proven in Lean, their
  * examples and probes evaluated there. End to end against Lean (see LeanLab).
  */
class LeanAritySuite extends LeanLab:
  private def evals(c: NodeCheck, prefix: String) = c.obligations.filter(_.name.lean.startsWith(prefix)).map(_.status.toString)

  test("a contract of one input: its code proven, its examples and probes evaluated in Lean") {
    val r = workflow(clampKb.implementProven(clamp)(clampAtZero)).check()
    assert(r.forall(_._2.status.toString == "proven"), r)
    val c = of(r, "Clamp")
    assertEquals(result(c, "impl").map(_.status.toString), Some("proven"), c)
    assert(evals(c, "eval_").size == 3 && evals(c, "evalImpl_").forall(_ == "proven") && evals(c, "eval_").forall(_ == "proven"), c.obligations.map(o => o.name.lean -> o.status.toString))
    assert(evals(c, "probe").nonEmpty && evals(c, "probe").forall(_ == "proven"), c.obligations.map(o => o.name.lean -> o.status.toString))
    assertEquals(result(of(r, "NeverBelowZero"), "root_impl").map(_.status.toString), Some("proven"), of(r, "NeverBelowZero"))
  }

  test("a contract of three inputs: its code proven, its examples and probes evaluated in Lean") {
    val r = workflow(grantKb.implementProven(grant)(grantIfMember)).check()
    assert(r.forall(_._2.status.toString == "proven"), r)
    val c = of(r, "Grant")
    assertEquals(result(c, "impl").map(_.status.toString), Some("proven"), c)
    assert(evals(c, "eval_").size == 4 && evals(c, "evalImpl_").forall(_ == "proven") && evals(c, "eval_").forall(_ == "proven"), c.obligations.map(o => o.name.lean -> o.status.toString))
    assert(evals(c, "probe").nonEmpty && evals(c, "probe").forall(_ == "proven"), c.obligations.map(o => o.name.lean -> o.status.toString))
  }

  test("an invariant kept by a contract of three inputs is proven from its view") {
    val r = workflow(betweenKb).check()
    assert(r.forall(_._2.status.toString == "proven"), statuses(r))
    def obligations(id: String) = of(r, id).obligations.map(o => o.name.lean -> o.status.toString)
    assertEquals(result(of(r, "PickBetween"), "cover_InStock").map(_.status.toString), Some("proven"), obligations("PickBetween"))
    assertEquals(result(of(r, "InStock"), "complete").map(_.status.toString), Some("proven"), obligations("InStock"))
  }

  test("a flow of two inputs: proven on the model, its examples evaluated in Lean, run in IO on an implementation") {
    val r = workflow(deliveriesKb).check()
    val c = of(r, "TwoDeliveries")
    assertEquals(c.status.toString, "proven", c)
    assert(evals(c, "eval_").nonEmpty && evals(c, "eval_").forall(_ == "proven"), c.obligations.map(o => o.name.lean -> o.status.toString))
    val counter = Counter(10)
    assertEquals(deliveriesKb.run[IO](twoDeliveries)(stock.bind(counter))(BigInt(2), BigInt(3)).unsafeRunSync(), BigInt(15))
    assertEquals(counter.held, BigInt(15))
  }

  test("a contract of no input: its code proven, its examples evaluated in Lean under their bindings") {
    val r = workflow(gaugeKb.implementProven(shows)(showRaw)).check()
    assert(r.forall(_._2.status.toString == "proven"), statuses(r))
    val c = of(r, "Shows")
    assertEquals(result(c, "impl").map(_.status.toString), Some("proven"), c)
    assert(evals(c, "eval_").size == 3 && (evals(c, "eval_") ++ evals(c, "evalImpl_")).forall(_ == "proven"),
      c.obligations.map(o => o.name.lean -> o.status.toString))
    assertEquals(result(of(r, "ShowsNow"), "root_impl").map(_.status.toString), Some("proven"), of(r, "ShowsNow"))
  }

  test("a flow of no input: proven on the model, its examples evaluated in Lean") {
    val c = of(workflow(countingKb).check(), "Counting")
    assertEquals(c.status.toString, "proven", c)
    assert(evals(c, "eval_").size == 3 && evals(c, "eval_").forall(_ == "proven"), c.obligations.map(o => o.name.lean -> o.status.toString))
  }


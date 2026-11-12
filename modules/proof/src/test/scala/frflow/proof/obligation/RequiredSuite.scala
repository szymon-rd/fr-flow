package frflow.proof.obligation

import frflow.core.analysis.resolution.Resolved
import frflow.core.name.NodeId
import frflow.proof.layout.Mini
import frflow.proof.layout.Handed
import frflow.proof.terms.TermTable

/** One test per rule of what must hold of a node (`Required`): `complete`, `feasible`, `impl`, and `made_` at a
  * call of plain Scala.
  */
class RequiredSuite extends munit.FunSuite:
  private def names(r: Resolved, n: String, authored: Set[(NodeId, ObligationName)] = Set.empty) =
    Required.of(r, authored, NodeId(n)).map(o => o.name -> o.discharge)
  private val (allowsOne, complete) = (NodeId("allowsOne"), ObligationName.Complete)

  test("complete: a node with parts and no proven code, made by its parts") {
    assertEquals(names(Mini.resolved, "allowsOne"), List(complete -> Discharge.Auto))
    assertEquals(Required.complete(Mini.resolved, allowsOne), Some(Prop.over(List(allowsOne),
      Prop.Implies(List(Hyp.of(NodeId("allowedPositive"))), Prop.claim(allowsOne)))))
  }

  test("feasible: asked of an authored complete only when what is below it is not witnessed, or authored itself") {
    val authored = Set(allowsOne -> complete)
    assertEquals(names(Mini.resolved, "allowsOne", authored), List(complete -> Discharge.Authored))
    assertEquals(names(Mini.resolved, "allowsOne", authored + (allowsOne -> ObligationName.Feasible)),
      List(complete -> Discharge.Authored, ObligationName.Feasible -> Discharge.Authored))
    val r = Unwitnessed.resolved
    val feasible = Required.of(r, Set(allowsOne -> complete), allowsOne).filter(_.name == ObligationName.Feasible)
    assertEquals(feasible.map(_.goal), List(Prop.Exists(List(allowsOne, NodeId("grows")),
      Prop.Both(cats.data.NonEmptyList.one(Prop.claim(NodeId("grows")))))))
    assertEquals(feasible.map(_.discharge), List(Discharge.Auto))
  }

  test("impl: a node about a Definition with proven code, from what its code relies on") {
    assertEquals(names(Mini.resolved, "bookRuns"), List(ObligationName.Impl -> Discharge.Auto))
  }

  test("made_ at the call reads through proven code, and assumes nothing of what the code binds (review 11b)") {
    val declared = AlwaysSuite().declared(frflow.proof.layout.Laid(Handed.resolved, Map.empty, Nil), Handed.resolved)
    // Through a define on the spot and another Definition's code: the swapped booking reaches `ok`.
    val swapped = "((b.«end» : Int) < (b.start : Int))"
    List("spotCode", "definitionCode").foreach(c => assert(declared.linesIterator.dropWhile(l =>
      !l.contains(s"makes_${c}_call_0")).drop(1).next().contains(swapped), c))
    // Of each booking a tested function gives: that it is one of them, nothing more.
    assert(declared.contains("(∀ (x : Booking), ((x ∈ (twice b)) → (x.start < x.«end»)))"), declared)
  }

  test("an assumption of always is kept by the covered code making its values, as a claim is; only the claim is " +
      "asked of the values from outside (outside), which the assumption says itself") {
    def claimed(r: Resolved) = names(r, "endsAfterStart").map(_._1)
    assertEquals(names(Mini.resolved, "fromTheForm").map(_._1) :+ ObligationName.Outside, claimed(Mini.resolved))
  }

  test("the table of open terms the rules apply declarations to") {
    assertEquals(TermTable.of(Mini.resolved).claims(allowsOne).symbols.map(_.value), List("allowed"))
  }

package frflow.proof.obligation

import frflow.core.Lang
import frflow.core.analysis.{Resolved, Scope}
import frflow.core.name.NodeId
import frflow.core.ty.Ty
import frflow.proof.layout.{Broken, Mini, Programs, ProgramsProject}
import frflow.proof.layout.calls.{Handed, Reuse, Rows}
import frflow.proof.layout.failing.Failing
import frflow.proof.lean.print.Print
import frflow.proof.terms.TermTable

/** One test per rule of what must hold of a node (`Required`): `complete`, `feasible`, `impl`, `cover_<op>`, `made_`
  * of a define, of a program and of a store's operation, and `commute_i` of a pair and of a traverse at once.
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
    assertEquals(names(Programs.resolved, "fetchRuns").map(_._1), List(ObligationName.Impl))
  }

  test("cover_: an always kept by each program writing a store it is about, and by no other program") {
    assertEquals(names(Mini.resolved, "endsAfterStart").map(_._1).filter(_.isInstanceOf[ObligationName.Cover]),
      List(ObligationName.Cover("book")))
    assert(!names(Programs.resolved, "endsAfterStart").exists(_._1.isInstanceOf[ObligationName.Cover]))
  }

  test("made_ at the call: what proven code hands an operation on a state meets the rule, at every call (owner §37)") {
    assertEquals(names(Mini.resolved, "endsAfterStart").map(_._1).filterNot(_.isInstanceOf[ObligationName.Cover]),
      List(ObligationName.Made("bookIfFree_call_0")))
    assertEquals(names(Broken.resolved, "endsAfterStart").map(_._1).collect { case ObligationName.Made(m)
      if m.contains("_call_") => m }, List("fileBack_call_0", "putBoth_call_0", "putBoth_call_1"))
    // Programs calls no plain Scala: none is asked.
    assert(!names(Programs.resolved, "endsAfterStart").exists(n => n._1.toString.contains("_call_")))
  }

  test("made_ at the call reads through proven code, and assumes nothing of what the code binds (review 11b)") {
    val declared = AlwaysSuite().declared(frflow.proof.layout.Laid(Handed.resolved, Map.empty, Nil), Handed.resolved)
    // Through a define on the spot and another Definition's code: the swapped booking reaches `ok`.
    val swapped = "((b.«end» : Int) < (b.start : Int))"
    List("spotCode", "definitionCode").foreach(c => assert(declared.linesIterator.dropWhile(l =>
      !l.contains(s"makes_${c}_call_0")).drop(1).next().contains(swapped), c))
    // Of each booking a tested function gives: that it is one of them, nothing more.
    assert(declared.contains("(∀ (x : Booking), ((x ∈ (twice b)) → (x.start < x.«end»)))"), declared)
    // Of a branch's result: nothing (the seeded duplicate, not assumed away).
    val branch = AlwaysSuite().declared(frflow.proof.layout.Laid(Rows.resolved(Rows.viaBranch), Map.empty, Nil),
      Rows.resolved(Rows.viaBranch))
    assert(branch.contains("(∀ (r : (List Int)), (List.Nodup r))"), branch)
  }

  test("an operation's result is not trusted after a write that may run before it: a loop's, a failed body's") {
    List(Reuse.inLoop -> "makes_expireIt_call_1", Reuse.inHandler -> "makes_expireIt_call_3").foreach { (steps, at) =>
      val declared = AlwaysSuite().declared(frflow.proof.layout.Laid(Reuse.resolved(steps), Map.empty, Nil),
        Reuse.resolved(steps))
      val stated = declared.linesIterator.dropWhile(!_.contains(at)).drop(1).next()
      assert(stated.contains("(∀ (r : (List Int)), (List.Nodup r))"), stated)
    }
  }

  test("made_ at the call, crm-shaped: what the job hands storeAbout holds each key once, below the job's branch") {
    List(Rows.once, Rows.duplicates).foreach(steps =>
      assertEquals(names(Rows.resolved(steps), "onePerKey"), List(ObligationName.Made("expireIt_call_0") ->
        Discharge.Auto)))
    val declared = AlwaysSuite().declared(frflow.proof.layout.Laid(Rows.resolved(Rows.once), Map.empty, Nil),
      Rows.resolved(Rows.once))
    // Below the branch the store is called on: the rows not holding the key.
    assert(declared.contains("makes_expireIt_call_0") && declared.contains("(¬"), declared)
  }

  test("made_: of a define making what the always is about, and of a program whose run gives one") {
    assertEquals(names(Programs.resolved, "endsAfterStart").map(_._1),
      List(ObligationName.Made("reschedule"), ObligationName.Made("fetch"), ObligationName.Made("latest"),
        ObligationName.Made("sample")))
    val made = Required.made(Programs.resolved, NodeId("endsAfterStart"))
    assertEquals(made.map(_.doc).take(2), List("Every result of later meets endsAfterStart.",
      "Every result of a run of fetchOne_run meets endsAfterStart."))
  }

  test("made_ of a store's operation: on its model, over a world meeting what always holds") {
    val made = Required.made(Programs.resolved, NodeId("endsAfterStart"))
      .filter(_.name == ObligationName.Made("sample"))
    assertEquals(made.map(o => (o.goal, o.doc)), List((Prop.over(Nil, Prop.Makes(NodeId("endsAfterStart"),
      frflow.core.name.SymbolName("sample"), made.head.goal match
        case Prop.Forall(_, m: Prop.Makes) => m.formula
        case _                              => fail("not a maker's statement"),
      Map(frflow.core.name.SymbolName("sample") -> Substitute.Code(frflow.core.name.DefName("Shelved.sample_of"))))),
      "Every result of shelved's sample meets endsAfterStart, on a world meeting what always holds.")))
    assertEquals(Required.made(Mini.resolved, NodeId("endsAfterStart")), Nil) // `add` gives no booking
  }

  test("commute_: a pair at once and a traverse at once, each in either order") {
    def commutes(n: String) = Required.commutes(Programs.resolved, NodeId(n))
    assertEquals(commutes("pairRuns").map(_.name), List(ObligationName.Commute(0)))
    assertEquals(commutes("eachRuns").map(_.name), List(ObligationName.Commute(0)))
    assertEquals(commutes("fetchRuns"), Nil)
    val each = commutes("eachRuns").head.goal match
      case Prop.Forall(_, Prop.Commutes(c, _)) => c
      case other                                => fail(s"not a commutation: $other")
    assertEquals((each.apart.map(a => (a.one.hint, a.two.hint)), each.result),
      (Some(("x_one", "x_two")), Ty.TupleOf(List(Lang.big, Lang.big))))
  }

  test("commute_ of steps at once on a store: reading it twice, adding to it twice") {
    assertEquals(Required.commutes(Broken.resolved, NodeId("countRuns")).map(_.name), List(ObligationName.Commute(0)))
    assertEquals(Required.commutes(Broken.resolved, NodeId("putRuns")).map(_.name), List(ObligationName.Commute(0)))
  }

  test("commute_ in Lean: both orders run on the models from every world") {
    val spec = ProgramsProject.modules.find(_.name.dotted == "FrFlowGen.Test.pairRuns.Spec").map(Print.module)
    val expected = """@[frflow_defs] def commute_0 : Prop :=
      |  ∀ (n : Int) (w : World), FrFlow.runOn ((do
      |        let a ← pure n
      |        let c ← pure (n + (1 : Int))
      |        pure (a, c)) : StateM World (Int × Int)) w = FrFlow.runOn ((do
      |        let c ← pure (n + (1 : Int))
      |        let a ← pure n
      |        pure (a, c)) : StateM World (Int × Int)) w""".stripMargin
    assert(spec.exists(_.contains(expected)), spec.getOrElse("no module"))
  }

  test("an assumption of always is kept by the covered code making or storing its values, as a claim is") {
    assertEquals(names(Programs.resolved, "fromOutside").map(_._1),
      names(Programs.resolved, "endsAfterStart").map(_._1))
    assertEquals(names(Mini.resolved, "fromTheForm").map(_._1), names(Mini.resolved, "endsAfterStart").map(_._1))
  }

  test("every op with proven code where an always must hold gets its cover_ or its made_") {
    for
      r  <- List(Mini.resolved, Programs.resolved, Broken.resolved, Failing.resolved)
      n  <- r.theory.nodes.map(_.node.id)
      op <- Scope.of(r.theory, n) if r.theory.code.attached.get(op).exists(_.code.proven.nonEmpty)
    do assert(names(r, n.value).exists((o, _) => o == ObligationName.Cover(op.value) ||
      o == ObligationName.Made(op.value)), s"${op.value} in the scope of ${n.value}: ${names(r, n.value)}")
  }

  test("the table of open terms the rules apply declarations to") {
    assertEquals(TermTable.of(Mini.resolved).claims(allowsOne).symbols.map(_.value), List("allowed"))
  }

package frflow.cli

import frflow.api.node.lean.{FindingView, Forbidden, Message, TryView}
import frflow.api.view.{Stop, Warning}
import frflow.cli.say.*
import frflow.core.analysis.Problem
import frflow.core.name.{NodeId, RelPath}
import frflow.decision.content.{Chain, Content}
import frflow.decision.ledger.{Action, Authorship, Bound, Decision, Reason, Uncounted}
import frflow.decision.review.{Cause, ReviewState, Unproven}
import frflow.decision.rules.Refusal
import frflow.dsl.build.Fault
import java.time.Instant

/** Every case the API returns has its words: each refusal, warning, stop, finding, unproven case and reason a decision
  * does not count, and the faults a model is written with; "not tested yet" is not "fails a generated case".
  */
class TextsSuite extends munit.FunSuite:
  private val (a, b) = (NodeId("a"), NodeId("b"))
  private val file = RelPath.fromIdentifiers("src", "A.scala")
  private val decision = Decision(Action.Accept, Authorship("ann", Instant.EPOCH, None), Reason("it holds here", Nil),
    Bound(Content.empty, Chain.empty, None), None, None)

  private def distinct(texts: List[String]): Unit =
    assert(texts.forall(_.trim.nonEmpty), texts)
    assertEquals(texts.distinct.size, texts.size, texts.mkString("\n"))

  test("every refusal is said, a failing case apart from code not tested yet, the claim's change apart from both") {
    val all = List(Refusal.NoOneDecides, Refusal.NoReason, Refusal.NoNodes, Refusal.NothingToConfirm,
      Refusal.UnknownNode(a), Refusal.NotADecider("bob"), Refusal.MovedSinceSeen(a),
      Refusal.NotAProposal(a, ReviewState.Accepted), Refusal.NotDecided(a), Refusal.AlreadyAccepted(a),
      Refusal.AlreadyRevisited(a), Refusal.AcceptFirst(a), Refusal.CodeFails(a), Refusal.NotTested(a),
      Refusal.Rewritten(List(a)), Refusal.NotBelow(a, List(b)), Refusal.StillInModel(a),
      Refusal.Within(b, Refusal.NoNodes))
    distinct(all.map(Refusals.text(_, _ => Nil)) :+ Refusals.text(Refusal.CodeFails(a), _ => List(Cause.Self)))
    assert(Refusals.text(Refusal.NotTested(a), _ => Nil).contains("not tested yet"))
    assert(Refusals.text(Refusal.CodeFails(a), _ => Nil).contains("fails a generated case"))
  }

  test("every warning is said, with why a decision does not count") {
    distinct(List(Warning.NoKey, Warning.DecidersUncommitted, Warning.GovernedTwice(file, List(a, b)),
      Warning.Ungoverned(file), Warning.GovernedMissing(file, a), Warning.ProofFileOfNoNode(file),
      Warning.ConsistencyNotProven(List(a)), Warning.StartNotProven(a), Warning.NotChecked(a), Warning.Restates(a, b))
      .map(Warnings.text) ++ Uncounted.values.toList.map(u => Warnings.text(Warning.NotCounted(a, decision, u))))
  }

  test("every stop, finding, try, forbidden form and unproven case is said") {
    distinct(List(Stop.NoLean, Stop.UnknownNode(a), Stop.NotJson("f", "p"), Stop.NoVersion("f"),
      Stop.UnknownVersion("f", 2, 1), Stop.BadField("f", 1, "x", "p"), Stop.NoKey("k"), Stop.NotAKey("k", "p"))
      .flatMap(Stops.lines))
    val m = List(Message("Lean.lean", 3, true, "unsolved goals"))
    distinct(List(FindingView.LeanTimedOut, FindingView.ModelDoesNotBuild(m), FindingView.LemmasDoNotBuild(m),
      FindingView.NotProven(m), FindingView.DisallowedAxioms(List("sorryAx")), FindingView.StepRefuted(Nil))
      .map(Findings.lines(_, full = false).mkString("\n")))
    distinct(List(TryView.Needed(a), TryView.Vacuous, TryView.Restates, TryView.Clash, TryView.Unsat, TryView.Idle,
      TryView.RestatesConjunct(a, 0)).map(Findings.tried))
    distinct(List(Forbidden.Axiom, Forbidden.Admit, Forbidden.Unsafe, Forbidden.Opaque, Forbidden.ImplementedBy,
      Forbidden.Extern, Forbidden.NativeDecide, Forbidden.Attribute, Forbidden.SetOption("o"),
      Forbidden.Metaprogram("m"), Forbidden.Import("i"), Forbidden.LemmaImport("i"), Forbidden.Command("c"))
      .map(Findings.forbidden))
    distinct(List(Unproven.Check, Unproven.Parts, Unproven.NotNeeded(a), Unproven.Clash, Unproven.NothingBelow,
      Unproven.Kept(a), Unproven.Implementation, Unproven.RootImpl, Unproven.Tests, Unproven.NotTested, Unproven.Idle,
      Unproven.Consistency).map(Unprovens.text))
    assertEquals(Unprovens.text(Unproven.NotTested), "not tested yet: run check")
  }

  test("a value only plain code reads, spoken of in a statement, says how to let a statement speak of it") {
    assertEquals(Faults.fault(Fault.CodeOnlyInStatement("Calendar")),
      "Calendar has no LeanType: add `derives LeanType` if a statement should speak of it")
    assert(Problems.text(Problem.CodeOnlyInStatement(a, frflow.core.name.SymbolName("cal"), "Calendar"))
      .contains("Calendar has no LeanType"))
    assert(Problems.text(Problem.NoRoot).startsWith("no root statement"))
  }

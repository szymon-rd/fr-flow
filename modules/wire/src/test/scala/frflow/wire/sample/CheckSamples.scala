package frflow.wire.sample

import frflow.core.name.NodeId
import frflow.proof.obligation.{ObligationName, TryKind}
import frflow.proof.reading.{Diagnostic, NotAllowed}
import frflow.core.expr.Value
import frflow.proof.verdict.{CheckKey, CheckStatus, Checks, Finding, NodeCheck, ObligationStatus, Result,
  WholeCheck}
import java.time.Instant

/** The golden checks: a node proven, one refused for its proof file, one refuted by a try. */
object CheckSamples:
  private val at = Instant.parse("2026-10-03T08:00:00Z")
  private val error = Diagnostic("Proofs/Rooms/Book.lean", 12, true, "unsolved goals")

  private val proven = NodeCheck(NodeId("Root"), CheckKey("4e1f0c"), CheckStatus.Proven, List(
    Result(ObligationName.Complete, ObligationStatus.Proven, Nil),
    Result(ObligationName.Cover("add"), ObligationStatus.Proven, Nil),
    Result(ObligationName.Tried(TryKind.Needed(NodeId("Free"))), ObligationStatus.NotShown, Nil),
    Result(ObligationName.Satisfiable(NodeId("Root"), 0), ObligationStatus.Shown, Nil)), Nil, at)

  private val refused = NodeCheck(NodeId("Book"), CheckKey("77aa01"), CheckStatus.Failed, List(
    Result(ObligationName.Impl, ObligationStatus.Open, List(error))), List(
    Finding.ProofNotAllowed(List(3 -> NotAllowed.NativeDecide, 5 -> NotAllowed.Import("Mathlib.Tactic"))),
    Finding.DisallowedAxioms(List("sorryAx"))), at)

  private val refuted = NodeCheck(NodeId("Free"), CheckKey("90bc12"), CheckStatus.Failed, List(
    Result(ObligationName.Tried(TryKind.Clash), ObligationStatus.Shown, Nil),
    Result(ObligationName.Tried(TryKind.RestatesConjunct(NodeId("Root"), 2)), ObligationStatus.NotShown, Nil)),
    List(Finding.Refuted(List(TryKind.Clash)), Finding.NotProven(List(error)), Finding.LeanTimedOut), at)

  private val stepRefuted = NodeCheck(NodeId("Small"), CheckKey("31d7e0"), CheckStatus.Open, List(
    Result(ObligationName.Complete, ObligationStatus.Open, Nil)), List(Finding.StepRefuted(List("n" -> Value.Num(4)))),
    at)

  private val whole = WholeCheck(CheckKey("5a6b7c"), List(
    Result(ObligationName.Consistent(0), ObligationStatus.Proven, Nil),
    Result(ObligationName.Inhabited(NodeId("EndsAfterStart")), ObligationStatus.Shown, Nil),
    Result(ObligationName.Example(0), ObligationStatus.NotShown, Nil)), at)

  val checks: Checks =
    Checks(List(proven, refused, refuted, stepRefuted).map(c => c.node -> c).toMap, Some(whole))

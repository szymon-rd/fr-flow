package frflow.wire.sample

import frflow.core.name.NodeId
import frflow.proof.obligation.{ObligationName, TryKind}
import frflow.proof.reading.{Diagnostic, NotAllowed}
import frflow.proof.verdict.{CheckKey, CheckStatus, Checks, Finding, NodeCheck, ObligationStatus, Result, WholeCheck}
import frflow.wire.sample.Draws.*
import org.scalacheck.Gen

/** Checks: every obligation name, try, rule and finding. */
object CheckDraws:
  private val small = Gen.choose(-2, 12)

  val tryKind: Gen[TryKind] = Gen.oneOf(node.map(TryKind.Needed(_)), Gen.oneOf(TryKind.Vacuous, TryKind.Restates,
    TryKind.Clash, TryKind.Unsat, TryKind.Idle), Gen.zip(node, small).map(TryKind.RestatesConjunct(_, _)))

  val obligation: Gen[ObligationName] = Gen.oneOf(
    Gen.oneOf(ObligationName.Complete, ObligationName.Feasible, ObligationName.Impl, ObligationName.RootImpl),
    word.map(ObligationName.Cover(_)), word.map(ObligationName.Made(_)), tryKind.map(ObligationName.Tried(_)),
    small.map(ObligationName.Commute(_)), small.map(ObligationName.Consistent(_)), node.map(ObligationName.Start(_)),
    node.map(ObligationName.Inhabited(_)), Gen.zip(node, small).map(ObligationName.Satisfiable(_, _)),
    small.map(ObligationName.Example(_)))

  val diagnostic: Gen[Diagnostic] = Gen.zip(text, small, Gen.oneOf(true, false), text).map(Diagnostic(_, _, _, _))

  val rule: Gen[NotAllowed] = Gen.oneOf(Gen.oneOf(NotAllowed.Axiom, NotAllowed.Admit, NotAllowed.Unsafe,
    NotAllowed.Opaque, NotAllowed.ImplementedBy, NotAllowed.Extern, NotAllowed.NativeDecide, NotAllowed.Attribute),
    text.map(NotAllowed.SetOption(_)), text.map(NotAllowed.Metaprogram(_)), text.map(NotAllowed.Import(_)),
    text.map(NotAllowed.LemmaImport(_)), text.map(NotAllowed.Command(_)))

  val finding: Gen[Finding] = Gen.oneOf(Gen.const(Finding.LeanTimedOut),
    few(diagnostic).map(Finding.ModelDoesNotBuild(_)), few(Gen.zip(small, rule)).map(Finding.ProofNotAllowed(_)),
    few(diagnostic).map(Finding.LemmasDoNotBuild(_)), few(diagnostic).map(Finding.NotProven(_)),
    few(tryKind).map(Finding.Refuted(_)), few(text).map(Finding.DisallowedAxioms(_)),
    few(Gen.zip(word, TestDraws.value(2))).map(Finding.StepRefuted(_)))

  val result: Gen[Result] =
    Gen.zip(obligation, Gen.oneOf(ObligationStatus.values.toList), few(diagnostic)).map(Result(_, _, _))

  def check(id: NodeId): Gen[NodeCheck] = Gen.zip(hex, Gen.oneOf(CheckStatus.values.toList), few(result),
    few(finding), instant).map((key, status, rs, fs, at) => NodeCheck(id, CheckKey(key), status, rs, fs, at))

  /** Each check under its own node, as the file keys them. */
  val nodes: Gen[Map[NodeId, NodeCheck]] = few(node.flatMap(id => check(id).map(id -> _))).map(_.toMap)

  val whole: Gen[WholeCheck] =
    Gen.zip(hex, few(result), instant).map((key, rs, at) => WholeCheck(CheckKey(key), rs, at))

  /** The nodes' checks, and the theory's when it has one. */
  val checks: Gen[Checks] = Gen.zip(nodes, Gen.option(whole)).map(Checks(_, _))

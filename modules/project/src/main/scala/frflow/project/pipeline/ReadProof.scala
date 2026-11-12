package frflow.project.pipeline

import frflow.core.analysis.outside.{Guards, Reads}
import frflow.core.analysis.resolution.Constrained
import frflow.core.checking.Checking
import frflow.core.code.Code
import frflow.core.graph.Walk
import frflow.core.name.NodeId
import frflow.core.spec.{Node, NodeKind, Range}
import frflow.core.ty.Ty
import frflow.core.vocab.SymbolType
import frflow.decision.review.{ProofStanding, Unproven}
import frflow.proof.audit.Obligations
import frflow.proof.obligation.{Made, ObligationName}
import frflow.proof.obligation.ObligationName.{Complete, Consistent, Impl, Inhabited, RootImpl, Tried}
import frflow.proof.obligation.TryKind.{Clash, Idle, Needed}
import frflow.proof.verdict.{CheckStatus, ObligationStatus, Result}
import frflow.proof.verdict.ObligationStatus.{NotShown, Proven, Shown}
import frflow.testing.report.{Outcome, TestReport}

/** What of a node is not proven again, whether its parts make it and whether Rocq proves its code, read off its
  * current check, its current tests and the theory's consistency: today's `Proofs.unproven` and `Mechanical.partsMake`,
  * line for line, less the examples (nothing depends on them) and with consistency (owner §18). A check or a report
  * whose key moved is not current, so it proves nothing.
  */
object ReadProof:
  def of(a: Analysis, n: Node): ProofStanding =
    val rs = a.current(n.id).toList.flatMap(_.results)
    ProofStanding(unproven(a, n, rs), partsMake(a, n.id, rs), codeProven(rs))

  private def unproven(a: Analysis, n: Node, rs: List[Result]): List[Unproven] =
    val (before, after) = local(a, n, rs)
    (before ++ kept(a, n.id, rs) ++ after).distinct

  /** Its own standing, all but what rests on the rules it takes: its check, its obligations and tries, nothing below
    * it; and the makers below its step, its tests, its consistency.
    */
  private def local(a: Analysis, n: Node, rs: List[Result]): (List[Unproven], List[Unproven]) =
    (List(check(a, n), open(rs), nothingBelow(a, n)).flatten,
      List(made(a, n.id), tests(a, n.id), consistent(a, n.id)).flatten)

  private def check(a: Analysis, n: Node): List[Unproven] =
    val proven = a.current(n.id).exists(_.status == CheckStatus.Proven)
    Option.when(n.statement.stated && !proven)(Unproven.Check).toList

  /** Each obligation it was asked that is not proven, each try that shows something wrong. */
  private def open(rs: List[Result]): List[Unproven] = rs.collect {
    case Result(Complete, s, _) if s != Proven      => Unproven.Parts
    case Result(Tried(Needed(p)), Shown, _)         => Unproven.NotNeeded(p)
    case Result(Tried(Clash), Shown, _)             => Unproven.Clash
    case Result(Impl, s, _) if s != Proven          => Unproven.Implementation
    case Result(RootImpl, s, _) if s != Proven      => Unproven.RootImpl
    case Result(Tried(Idle), Shown, _)              => Unproven.Idle
  }

  /** A claim nothing checks: no parts, and no code proven or tested against it, nor where its values are made or
    * kept (a hypothesis callers' proofs take, or a test its statement cannot have, checks nothing).
    */
  private def nothingBelow(a: Analysis, n: Node): List[Unproven] =
    val t = a.decided.theory
    val checked = Checking.of(t, n.id).exists {
      case Checking.FromParts(_) | Checking.AgainstCode(_, _) | Checking.TestedAgainst(_, _) |
          Checking.WhereMade(_, _) | Checking.SaysWhatIs(_, _) => true
      case _ => false
    }
    val leaf = n.statement.kind == NodeKind.Claim && t.refinement.parts(n.id).isEmpty && !checked
    Option.when(leaf)(Unproven.NothingBelow).toList

  /** Each rule it rests on whose own standing is not proven, for any reason (`local`: its check, its obligations,
    * its tests, its consistency), or which a source of its values leaves open (`attributed`): of a statement taking
    * a rule as a hypothesis (`Reads.taken`), each such rule, and of an `always`, itself; and through each obligation
    * of a rule, the rules it takes in turn (`Obligations.takes`, one case per kind), all the way down. A rule open
    * only through another is named by that other: `Kept` names where the standing fails. The rules are kept together,
    * a joint induction, so a cycle of rules each proven of its own is settled proven, and one open makes every rule
    * reaching it open.
    */
  private def kept(a: Analysis, id: NodeId, rs: List[Result]): List[Unproven] =
    val t = a.decided.theory
    def results(rule: NodeId) = if rule == id then rs else a.current(rule).toList.flatMap(_.results)
    def takes(x: NodeId) = results(x).map(_.name).distinct.flatMap(Obligations.takes(a.decided, x, _))
    def below(rule: NodeId) = takes(rule).filter(r => t.node(r).exists(_.statement.rule))
    def own(rule: NodeId) = t.node(rule).exists(n => local(a, n, results(rule)) != (Nil, Nil)) || attributed(a, rule)
    val start = (if t.node(id).exists(_.statement.rule) then List(id) else Nil) ++ Reads.taken(t, id) ++ below(id)
    Walk.breadthFirst(start.distinct, identity)(below).filter(own).map(Unproven.Kept(_)).distinct

  /** What leaves a rule open beyond its own obligations: a value no rule allows (its `inhabited_` not proven: what
    * rests on a rule nothing meets is proven of nothing); of an `always[T]`, any test of tested plain Scala making a
    * `T` failing, missing or stale (its search stops at the first failing case, the post's perhaps), or tested by no
    * node at all, so never tried against the rule. Tested code handed a `T` makes none: what it is handed is drawn
    * meeting the rules, or is a proven caller's, asked at the call (`made_<code>_call_<i>`).
    */
  private def attributed(a: Analysis, rule: NodeId): Boolean =
    val t = a.decided.theory
    val proven = a.wholeCheck.toList.flatMap(_.results).collect { case Result(n, Proven, _) => n }.toSet
    val vacant = a.whole.exists(_.name == Inhabited(rule)) && !proven(Inhabited(rule))
    vacant || t.node(rule).flatMap(_.statement.range).exists {
      case Range.Made(ty) =>
        val makers = t.code.attached.toList.collect { case (s, at) if at.code.isInstanceOf[Code.Tested] &&
            Guards.applies(t, ty, resultOf(t, s)) => s }
        val testing = t.nodes.map(_.node.id).filter(Testable.of(t, _))
        makers.exists { m =>
          val reports = testing.filter(n => Constrained.of(t, n).contains(m))
          reports.isEmpty || reports.exists(n => red(a.tested(n)))
        }
      case Range.Possible => false
    }

  private def resultOf(t: frflow.core.Theory, s: frflow.core.name.SymbolName): Ty =
    t.vocabulary.symbol(s).map(_.ty).collect { case SymbolType.Typed(ty) => Ty.resultOf(ty) }.getOrElse(Ty.Unit)

  /** Of a step taking what the makers below it make (`Made.taken`), each rule whose `made_<maker>` is not proven, or
    * the `made_` of a maker it calls, which that `made_` takes (`Made.resting`): the step rests on each (step 12
    * ruling), so a maker breaking the rule through its callee leaves the step unproven too.
    */
  private def made(a: Analysis, id: NodeId): List[Unproven] =
    Made.taken(a.decided, id).collect { case (rule, op, _) if Made.resting(a.decided, rule, op).exists(m =>
      !a.current(rule).exists(_.results.exists(r => r.name == ObligationName.Made(m.value) && r.status == Proven))) =>
      Unproven.Kept(rule) }.distinct

  /** At the bottom, the group it shares open values with not proven to hold together; proven from parts, a
    * statement below it
    * about a Declaration in a group not proven (owner §28: its step takes what the Declarations are as hypotheses,
    * and only their group shows they can hold together). Each is its consistency not proven, and the proof is red.
    * Vacuity is warned of, not gated on.
    */
  private def consistent(a: Analysis, id: NodeId): List[Unproven] =
    val t = a.decided.theory
    val proven = a.wholeCheck.toList.flatMap(_.results).collect { case Result(n, Proven, _) => n }.toSet
    val open = a.groups.filterNot((i, _) => proven(Consistent(i))).flatMap(_._2).toSet
    val below = Walk.breadthFirst(t.refinement.parts(id), identity)(t.refinement.parts).filter(n =>
      open(n) && Constrained.of(t, n).exists(Constrained.isDeclaration(t, _)))
    Option.when(open(id) || below.nonEmpty)(Unproven.Consistency).toList

  /** Its plain code tested: a current report with no failing case, every case asked tried, every part reached (none
    * since it moved: not tested yet). A statement with no Scala value is not checked by its tests, which is no
    * failure.
    */
  private def tests(a: Analysis, id: NodeId): List[Unproven] =
    Option.when(Testable.of(a.decided.theory, id))(a.tested(id)).toList.flatMap(_.fold(List(Unproven.NotTested))(r =>
      Option.when(failing(r))(Unproven.Tests).toList))

  /** A report with a failing case, a case asked not tried, or a part not reached. */
  private def failing(r: TestReport): Boolean = r.outcome match
    case Outcome.NotChecked(_) => false
    case Outcome.Failed(_)     => true
    case Outcome.Passed        => r.unreached.nonEmpty || r.count.shortfall > 0

  /** A report missing (not run since the code moved), or failing. */
  private def red(r: Option[TestReport]): Boolean = r.forall(failing)

  /** `complete` proven, every `needed_C` not shown, no clash shown; and it has parts. */
  private def partsMake(a: Analysis, id: NodeId, rs: List[Result]): Boolean =
    a.decided.theory.refinement.parts(id).nonEmpty && status(rs, Complete).contains(Proven) &&
      !status(rs, Tried(Clash)).contains(Shown) &&
      rs.forall { case Result(Tried(Needed(_)), s, _) => s == NotShown; case _ => true }

  /** Rocq proves its code: an `impl` or `root_impl` asked of it, and proven; tested code is not. */
  private def codeProven(rs: List[Result]): Boolean = rs.exists {
    case Result(Impl | RootImpl, Proven, _) => true
    case _                                  => false
  }

  private def status(rs: List[Result], name: ObligationName): Option[ObligationStatus] =
    rs.find(_.name == name).map(_.status)

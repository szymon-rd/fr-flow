package frflow.project.pipeline

import frflow.core.analysis.Scope
import frflow.core.checking.Checking
import frflow.core.name.NodeId
import frflow.core.spec.{Node, NodeKind}
import frflow.decision.review.{ProofStanding, Unproven}
import frflow.proof.obligation.ObligationName
import frflow.proof.obligation.ObligationName.{Complete, Consistent, Cover, Impl, RootImpl, Start, Tried}
import frflow.proof.obligation.TryKind.{Clash, Idle, Needed}
import frflow.proof.verdict.{CheckStatus, ObligationStatus, Result}
import frflow.proof.verdict.ObligationStatus.{NotShown, Proven, Shown}
import frflow.testing.report.Outcome

/** What of a node is not proven again, whether its parts make it and whether Lean proves its code, read off its
  * current check, its current tests and the theory's consistency: today's `Proofs.unproven` and `Mechanical.partsMake`,
  * line for line, less the examples (nothing depends on them) and with consistency (owner §18). A check or a report
  * whose key moved is not current, so it proves nothing.
  */
object ReadProof:
  def of(a: Analysis, n: Node): ProofStanding =
    val rs = a.current(n.id).toList.flatMap(_.results)
    ProofStanding(unproven(a, n, rs), partsMake(a, n.id, rs), codeProven(rs))

  private def unproven(a: Analysis, n: Node, rs: List[Result]): List[Unproven] =
    List(check(a, n), open(rs), nothingBelow(a, n), kept(a, n.id, rs), tests(a, n.id), consistent(a, n.id)).flatten

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
      case Checking.FromParts(_) | Checking.AgainstCode(_, _) | Checking.TestedAgainst(_, _) | Checking.KeptBy(_) |
          Checking.WhereMade(_, _, _) => true
      case _ => false
    }
    val leaf = n.statement.kind == NodeKind.Claim && t.refinement.parts(n.id).isEmpty && !checked
    Option.when(leaf)(Unproven.NothingBelow).toList

  /** Of an `always`, each program keeping it whose `cover_<op>` is not proven. */
  private def kept(a: Analysis, id: NodeId, rs: List[Result]): List[Unproven] =
    Option.when(Scope.of(a.decided.theory, id).exists(op => !status(rs, Cover(op.value)).forall(_ == Proven)))(
      Unproven.Kept(id)).toList

  /** At the bottom, the group it shares open values with not proven to hold together; of what always holds of a
    * store, the states it starts in not proven to meet it (`start_<node>`): either is its consistency not proven.
    * Vacuity is warned of, not gated on.
    */
  private def consistent(a: Analysis, id: NodeId): List[Unproven] =
    val proven = a.wholeCheck.toList.flatMap(_.results).collect { case Result(n, Proven, _) => n }.toSet
    val start = a.whole.exists(_.name == Start(id)) && !proven(Start(id))
    val group = a.groups.exists((i, ids) => ids.contains(id) && !proven(Consistent(i)))
    Option.when(group || start)(Unproven.Consistency).toList

  /** Its plain code, or a store's implementations, tested: a current report with no failing case, every case asked
    * tried, every part reached (none since it moved: not tested yet). A statement with no Scala value is not checked
    * by its tests, which is no failure.
    */
  private def tests(a: Analysis, id: NodeId): List[Unproven] =
    val tested = Testable.of(a.decided.theory, id) || a.modelled(id)
    a.tested(id).fold(Option.when(tested)(Unproven.NotTested).toList)(r => Option.when(tested && (r.outcome match
      case Outcome.NotChecked(_) => false
      case Outcome.Failed(_)     => true
      case Outcome.Passed        => r.unreached.nonEmpty || r.count.shortfall > 0))(Unproven.Tests).toList)

  /** `complete` proven, every `needed_C` not shown, no clash shown; and it has parts. */
  private def partsMake(a: Analysis, id: NodeId, rs: List[Result]): Boolean =
    a.decided.theory.refinement.parts(id).nonEmpty && status(rs, Complete).contains(Proven) &&
      !status(rs, Tried(Clash)).contains(Shown) &&
      rs.forall { case Result(Tried(Needed(_)), s, _) => s == NotShown; case _ => true }

  /** Lean proves its code: an `impl` or `root_impl` asked of it, and proven; tested code is not. */
  private def codeProven(rs: List[Result]): Boolean = rs.exists {
    case Result(Impl | RootImpl, Proven, _) => true
    case _                                  => false
  }

  private def status(rs: List[Result], name: ObligationName): Option[ObligationStatus] =
    rs.find(_.name == name).map(_.status)

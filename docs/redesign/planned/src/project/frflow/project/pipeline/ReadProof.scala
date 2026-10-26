package frflow.project.pipeline

import frflow.core.graph.Edge
import frflow.core.name.NodeId
import frflow.core.spec.{Node, NodeKind}
import frflow.decision.review.{ProofStanding, Unproven}
import frflow.eval.run.{Agreement, ExampleResult}
import frflow.proof.obligation.ObligationName
import frflow.proof.obligation.ObligationName.{Complete, Cover, Expect, Impl, RootImpl, Tried}
import frflow.proof.obligation.TryKind.{Clash, Idle, Needed}
import frflow.proof.verdict.{CheckStatus, ObligationStatus, Result}
import frflow.proof.verdict.ObligationStatus.{NotShown, Proven, Shown}

/** What of a node is not proven again and whether its parts make it, read off its current check, its examples and
  * its tests: today's `Proofs.unproven` and `Mechanical.partsMake`, line for line.
  */
object ReadProof:
  def of(a: Analysis, n: Node): ProofStanding =
    val rs = results(a, n.id)
    ProofStanding(unproven(a, n, rs), partsMake(a, n.id, rs))

  private def unproven(a: Analysis, n: Node, rs: List[Result]): List[Unproven] =
    List(check(a, n), open(rs), nothingBelow(a, n), examples(a, n.id), kept(a, n.id, rs), tests(a, n.id)).flatten

  private def check(a: Analysis, n: Node): List[Unproven] =
    val proven = a.inputs.recorded.checks.get(n.id).exists(_.status == CheckStatus.Proven)
    Option.when(n.statement.stated && !proven)(Unproven.Check).toList

  /** Each obligation it was asked that is not proven, each try that shows something wrong. */
  private def open(rs: List[Result]): List[Unproven] = rs.collect {
    case Result(Complete, s, _) if s != Proven      => Unproven.Parts
    case Result(Tried(Needed(p)), Shown, _)         => Unproven.NotNeeded(p)
    case Result(Tried(Clash), Shown, _)             => Unproven.Clash
    case Result(Impl, s, _) if s != Proven          => Unproven.Implementation
    case Result(RootImpl, s, _) if s != Proven      => Unproven.RootImpl
    case Result(Expect(i), s, _) if s != Proven     => Unproven.Expectation(i)
    case Result(Tried(Idle), Shown, _)              => Unproven.Idle
  }

  private def nothingBelow(a: Analysis, n: Node): List[Unproven] =
    val leaf = n.statement.kind == NodeKind.Claim && a.decided.theory.refinement.parts(n.id).isEmpty
    Option.when(leaf)(Unproven.NothingBelow).toList

  /** Its examples that disagree, on the promise or on the code. */
  private def examples(a: Analysis, id: NodeId): List[Unproven] =
    val failing = a.computed.examples.getOrElse(id, Nil).count(!agrees(_))
    Option.when(failing > 0)(Unproven.Examples(failing)).toList

  private def agrees(e: ExampleResult): Boolean =
    e.onPromise == Agreement.Agrees && e.onCode.forall(_ == Agreement.Agrees)

  /** Each invariant whose keep is not proven, by the keep's own status as today: its `cover_X` when one was made,
    * the invariant's `complete`, and this contract not shown unneeded for it.
    */
  private def kept(a: Analysis, id: NodeId, rs: List[Result]): List[Unproven] =
    a.decided.theory.edges.collect { case Edge.Keeps(`id`, i, _) => i }.filterNot { i =>
      val invariant = results(a, i)
      status(rs, Cover(i.value)).forall(_ == Proven) && status(invariant, Complete).contains(Proven) &&
        !status(invariant, Tried(Needed(id))).contains(Shown)
    }.map(Unproven.Invariant(_))

  /** Its plain code, or an outside system, tested: a report with no failing case and every part reached. */
  private def tests(a: Analysis, id: NodeId): List[Unproven] =
    val code = a.decided.theory.code
    val tested = code.attached.get(id).exists(_.code.proven.isEmpty) || code.realized.contains(id)
    val passed = a.inputs.recorded.tests.get(id).exists((_, r) => r.failure.isEmpty && r.unreached.isEmpty)
    Option.when(tested && !passed)(Unproven.Tests).toList

  /** `complete` proven, every `needed_C` not shown, no clash shown; and it has parts. */
  private def partsMake(a: Analysis, id: NodeId, rs: List[Result]): Boolean =
    a.decided.theory.refinement.parts(id).nonEmpty && status(rs, Complete).contains(Proven) &&
      !status(rs, Tried(Clash)).contains(Shown) &&
      rs.forall { case Result(Tried(Needed(_)), s, _) => s == NotShown; case _ => true }

  private def results(a: Analysis, id: NodeId): List[Result] =
    a.inputs.recorded.checks.get(id).toList.flatMap(_.results)

  private def status(rs: List[Result], name: ObligationName): Option[ObligationStatus] =
    rs.find(_.name == name).map(_.status)

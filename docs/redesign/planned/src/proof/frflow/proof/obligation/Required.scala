package frflow.proof.obligation

import cats.data.NonEmptyList
import frflow.core.analysis.Resolved
import frflow.core.name.NodeId

/** What must hold of a node, in today's order: `complete`, `feasible`, `impl`, `commute_i`, `check`, `cover_X`,
  * `expect_i`.
  */
object Required:
  def of(r: Resolved, authored: Set[(NodeId, ObligationName)], n: NodeId): List[Obligation] =
    def how(o: ObligationName) = if authored((n, o)) then Discharge.Authored else Discharge.Auto
    complete(r, n).map(Obligation(ObligationName.Complete, _, how(ObligationName.Complete), completes(r, n))).toList ++
      feasible(r, authored, n) ++ impl(r, n) ++ commutes(r, n) ++ check(r, n) ++ covers(r, n) ++ expects(r, n)

  /** `∀ U, C1 → … → Cn → N`. */
  def complete(r: Resolved, n: NodeId): Option[Prop] =
    NonEmptyList.fromList(r.theory.refinement.parts(n)).map(ps =>
      Prop.over(List(n), Prop.Implies(Hyp.parts(ps.toList), Prop.claim(n))))

  private def completes(r: Resolved, n: NodeId): String =
    s"The parts of ${n.value} (${r.theory.refinement.parts(n).map(_.value).mkString(", ")}) together make it."

  /** `∃ U, C1 ∧ … ∧ Cn`, asked of an authored `complete` on a node nothing witnesses. */
  private def feasible(r: Resolved, authored: Set[(NodeId, ObligationName)], n: NodeId): List[Obligation] = ???
  /** `∀ U, promises of the callees → claim[op := code]`: "Every result of D meets N, given what … promise." */
  private def impl(r: Resolved, n: NodeId): List[Obligation] = ???
  private def commutes(r: Resolved, n: NodeId): List[Obligation] = ???
  private def check(r: Resolved, n: NodeId): List[Obligation] = ???
  private def covers(r: Resolved, n: NodeId): List[Obligation] = ???
  /** `∀ U, N → expected_i`. */
  private def expects(r: Resolved, n: NodeId): List[Obligation] = ???

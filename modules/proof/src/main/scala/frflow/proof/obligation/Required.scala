package frflow.proof.obligation

import cats.data.NonEmptyList
import frflow.core.analysis.resolution.{Callees, Constrained, Resolved, SaysWhat}
import frflow.core.name.{NodeId, SymbolName}
import frflow.core.ty.Ty
import frflow.core.vocab.SymbolType

/** What must hold of a node, each read off its statement, its place and the code (owner §15), in today's order:
  * `complete` (proven from its parts), `feasible`, `impl` (checked against the proven code of the Definitions it
  * mentions), `made_<maker>` (an `always[T]` met by what each maker gives). What holds of the theory
  * as a whole (consistency, vacuity, the examples) is `Joint`'s.
  */
object Required:
  /** Each proven by FrFlow's automation, or by the theorem of its name in the node's proof file (`authored`). */
  def of(r: Resolved, authored: Set[(NodeId, ObligationName)], n: NodeId): List[Obligation] =
    (complete(r, n).map(Obligation(ObligationName.Complete, _, Discharge.Auto, completes(r, n))).toList ++
      feasible(r, authored, n) ++ impl(r, n) ++ Made.of(r, n) ++
      Made.atCalls(r, n) ++ Made.outside(r, n))
      .map(o => if authored((n, o.name)) then o.copy(discharge = Discharge.Authored) else o)

  /** `∀ U, C1 → … → Cn → M → N`, of a node not checked against proven code: its parts, and what the makers its parts'
    * claims are about make (`Made.taken`).
    */
  def complete(r: Resolved, n: NodeId): Option[Prop] =
    NonEmptyList.fromList(r.theory.refinement.parts(n)).filter(_ => SaysWhat.checkedAgainst(r.theory, n).isEmpty)
      .map(ps => Prop.over(List(n), Prop.Implies(Hyp.parts(ps.toList) ++ Made.taken(r, n).map(_._3),
        Prop.claim(n))))

  private def completes(r: Resolved, n: NodeId): String =
    s"The parts of ${n.value} (${r.theory.refinement.parts(n).map(_.value).mkString(", ")}) together make it."

  /** `∃ U, C1 ∧ … ∧ Cn`, asked of an authored `complete` on a node nothing witnesses. */
  private def feasible(r: Resolved, authored: Set[(NodeId, ObligationName)], n: NodeId): List[Obligation] =
    val asked = authored((n, ObligationName.Complete)) && (!Witnessed.below(r, n) ||
      authored((n, ObligationName.Feasible)))
    val how = if authored((n, ObligationName.Feasible)) then Discharge.Authored else Discharge.Auto
    NonEmptyList.fromList(r.theory.refinement.parts(n)).filter(_ => asked && complete(r, n).nonEmpty).toList.map(ps =>
      Obligation(ObligationName.Feasible, Prop.Exists(n :: ps.toList, Prop.Both(ps.map(Prop.claim))), how,
        s"Some world meets the parts of ${n.value}: its authored proof does not rest on a contradiction."))

  /** `∀ U, H → claim[ds := code]`: the statement asked of the proven code of every Definition it mentions at once
    * (each define): "Every result of D meets N, given what … promise"
    * (today's words). `H` is every part the node states (a design states nothing), the same code put in each where
    * it mentions the Definition: a part about a Definition the code calls, or about the node's own Definitions and
    * Declarations (sound: each part is checked against the same code, and `Validate` refuses a circle). A leaf's is
    * what its code relies on, as written: the statements about what the code calls (`Resolved.reliesOn`). A fixed
    * value the claim or its code reads stands as that value (2.7), in the claim and in each part reading it. The
    * members of a structure the claim reaches through its holder (`CodeTable.held`) are left as they are stated:
    * known by the parts, as what the holder's code calls is.
    */
  def impl(r: Resolved, n: NodeId): List[Obligation] =
    SaysWhat.checkedAgainst(r.theory, n).toList.map(reached(r, n, _)).map { c =>
      val hyps = hypotheses(r, n)
      val fixed = Fixed.of(r, (n :: hyps).flatMap(Constrained.of(r.theory, _)) ++ c.standsFor.keys)
      val code = c.standsFor.view.mapValues(Substitute.Code(_)).toMap ++ fixed
      val parts = r.theory.refinement.parts(n).toSet
      val assumed = hyps.map(h => if !parts(h) then Hyp.of(h)
        else Hyp(Hyp.of(h).name, Prop.ClaimOf(h, code.filter((s, _) => fixed.contains(s) || mentions(r, h, s)))))
      val goal = Prop.over(Nil, Prop.Implies(assumed, Prop.ClaimOf(n, code)))
      Obligation(ObligationName.Impl, goal, Discharge.Auto,
        (if c.standsFor.isEmpty then s"${n.value} holds"
          else s"Every result of ${c.standsFor.values.map(_.value).mkString(" and ")} meets ${n.value}") +
          givenWhat(hyps))
    }

  /** The code a node is asked of, less that of the structures it reaches through their holder. */
  private def reached(r: Resolved, n: NodeId, c: Callees): Callees =
    val through = Constrained.of(r.theory, n).flatMap(r.theory.code.held.getOrElse(_, Set.empty)).toSet
    c.copy(standsFor = c.standsFor.filterNot((s, _) => through(s)))

  /** What `impl` of a node rests on: the parts it states, or for a leaf what its code relies on. The circles
    * `Validate` refuses are walked along the same (`Resolve.circles`), a claim about other code that would close
    * one left out (`Relying`).
    */
  def hypotheses(r: Resolved, n: NodeId): List[NodeId] = r.provenFrom(n)

  private def mentions(r: Resolved, n: NodeId, s: SymbolName): Boolean = Constrained.of(r.theory, n).contains(s)

  private[obligation] def givenWhat(hyps: List[NodeId]): String =
    if hyps.isEmpty then "." else s", given what ${hyps.map(_.value).mkString(", ")} promise."

  private[obligation] def typeOf(r: Resolved, op: SymbolName): Option[Ty] =
    r.theory.vocabulary.symbol(op).map(_.ty).collect { case SymbolType.Typed(t) => t }

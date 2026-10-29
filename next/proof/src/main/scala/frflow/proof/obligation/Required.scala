package frflow.proof.obligation

import cats.data.NonEmptyList
import cats.syntax.all.*
import frflow.core.analysis.{Callees, Constrained, Resolved, SaysWhat, Scope}
import frflow.core.Failing
import frflow.core.term.interpret.Guard
import frflow.core.code.Code
import frflow.core.name.{DefName, NodeId, SymbolName}
import frflow.core.spec.CallForm
import frflow.core.ty.Ty
import frflow.core.vocab.SymbolType
import frflow.proof.terms.{Commutation, Keeping}
import frflow.core.analysis.outside.{Guards, Reads}

/** What must hold of a node, each read off its statement, its place and the code (owner §15), in today's order:
  * `complete` (proven from its parts), `feasible`, `impl` (checked against the proven code of the Definitions it
  * mentions), `cover_<op>` (an `always` kept by each program it applies to), `commute_i`. What holds of the theory
  * as a whole (consistency, vacuity, the examples) is `Joint`'s.
  */
object Required:
  /** Each proven by FrFlow's automation, or by the theorem of its name in the node's proof file (`authored`). */
  def of(r: Resolved, authored: Set[(NodeId, ObligationName)], n: NodeId): List[Obligation] =
    (complete(r, n).map(Obligation(ObligationName.Complete, _, Discharge.Auto, completes(r, n))).toList ++
      feasible(r, authored, n) ++ impl(r, n) ++ commutes(r, n) ++ keeps(r, n) ++ Made.of(r, n) ++
      Made.atCalls(r, n))
      .map(o => if authored((n, o.name)) then o.copy(discharge = Discharge.Authored) else o)

  /** `∀ U, C1 → … → Cn → N`, of a node not checked against proven code. */
  def complete(r: Resolved, n: NodeId): Option[Prop] =
    NonEmptyList.fromList(r.theory.refinement.parts(n)).filter(_ => SaysWhat.checkedAgainst(r.theory, n).isEmpty)
      .map(ps => Prop.over(List(n), Prop.Implies(Hyp.parts(ps.toList), Prop.claim(n))))

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
    * (each define, or a program's run on the models, `f_run`): "Every result of D meets N, given what … promise"
    * (today's words). `H` is every part the node states (a design states nothing), the same code put in each where
    * it mentions the Definition: a part about a Definition the code calls, or about the node's own Definitions and
    * Declarations (sound: each part is checked against the same code, and `Validate` refuses a circle). A leaf's is
    * what its code relies on, as written: the statements about what the code calls (`Resolved.reliesOn`).
    */
  def impl(r: Resolved, n: NodeId): List[Obligation] =
    SaysWhat.checkedAgainst(r.theory, n).toList.map { c =>
      val code = c.standsFor.view.mapValues(Substitute.Code(_)).toMap
      val hyps = hypotheses(r, n)
      val parts = r.theory.refinement.parts(n).toSet
      val assumed = hyps.map(h => if !parts(h) then Hyp.of(h)
        else Hyp(Hyp.of(h).name, Prop.ClaimOf(h, code.filter((s, _) => mentions(r, h, s)))))
      val goal = Prop.over(Nil, Prop.Implies(assumed, Prop.ClaimOf(n, code)))
      Obligation(ObligationName.Impl, goal, Discharge.Auto,
        s"Every result of ${c.standsFor.values.map(_.value).mkString(" and ")} meets ${n.value}" + givenWhat(hyps))
    }

  /** What `impl` of a node rests on: the parts it states, or for a leaf what its code relies on. */
  def hypotheses(r: Resolved, n: NodeId): List[NodeId] = r.provenFrom(n)

  private def mentions(r: Resolved, n: NodeId, s: SymbolName): Boolean = Constrained.of(r.theory, n).contains(s)

  private[obligation] def givenWhat(hyps: List[NodeId]): String =
    if hyps.isEmpty then "." else s", given what ${hyps.map(_.value).mkString(", ")} promise."

  /** `cover_<op>` of a statement of `always`, for each program it applies to whose code is proven and calls an
    * operation of a model the `always` is about (`Scope`): every run of the code keeps it, from a world meeting every
    * `always`, on inputs meeting theirs (`Keeping`), given what the code relies on. What covered code makes is asked of
    * it by `made`.
    */
  def keeps(r: Resolved, n: NodeId): List[Obligation] =
    val stores = r.theory.node(n).flatMap(_.statement.range).toList.flatMap(Scope.models(r.theory, _))
      .flatMap(_.ops.map(_.op))
    val writers = Scope.of(r.theory, n).filter(op =>
      Callees.ofDefinition(r.theory, op).exists(_.calls.operations.exists(stores.contains)))
    // The rule kept, and every rule taken, on the stores the program reads only (owner §33): another store's part of
    // the world is the run's frame.
    def reading(op: SymbolName) = Guards.reading(r.theory, Reads.ofProgram(r.theory, op))
    writers.flatMap(op => reading(op).toMap.get(n).map(op -> _)).flatMap { (op, kept) =>
      (Callees.ofDefinition(r.theory, op).flatMap(_.standsFor.get(op)), typeOf(r, op)).tupled.map { (code, ty) =>
        val escapes = Failing.escapingOf(r.theory, op).nonEmpty
        val within = reading(op).map(_._2)
        val goal = Prop.Keeps(n, op, Keeping.formula(op, ty, escapes)(inputs(r, op, ty), kept, within),
          Map(op -> Substitute.Code(code)))
        val hyps = r.reliedOnBy(op)
        Obligation(ObligationName.Cover(op.value), Prop.over(Nil, Prop.Implies(Hyp.parts(hyps), goal)),
          Discharge.Auto, s"Every run of ${code.value} keeps ${n.value}" + givenWhat(hyps))
      }
    }

  private[obligation] def typeOf(r: Resolved, op: SymbolName): Option[Ty] =
    r.theory.vocabulary.symbol(op).map(_.ty).collect { case SymbolType.Typed(t) => t }

  /** The run's inputs, named as a statement reading as its run names them, or by position. */
  private[obligation] def inputs(r: Resolved, op: SymbolName, ty: Ty): List[(String, Ty)] =
    r.theory.refinement.nodes.flatMap(_.statement.call).collectFirst {
      case CallForm.Run(`op`, post, _) => post.value.params.dropRight(3).map(x => x.hint -> x.ty)
    }.getOrElse(ty match
      case Ty.FnOf(ins, _) => ins.zipWithIndex.map((t, i) => s"x$i" -> t)
      case _               => Nil)

  /** `commute_i` of each parallel step of the proven programs `n` is checked against (`Commutation`), numbered
    * across them: either order of the branches gives the same result and leaves the same world.
    */
  def commutes(r: Resolved, n: NodeId): List[Obligation] =
    val flows = SaysWhat.checkedAgainst(r.theory, n).toList.flatMap(_.standsFor.keys).flatMap(op =>
      r.theory.code.attached.get(op).map(_.code).collect { case Code.ProvenFlow(f) => f })
    flows.distinct.flatMap(r.theory.vocabulary.define).flatMap(d => Commutation.of(r.theory.vocabulary, d).map(c =>
      (d, c))).zipWithIndex.map { case ((d, c), i) =>
      Obligation(ObligationName.Commute(i),
        Prop.over(Nil, Prop.Commutes(c, Callees.calledBy(r.theory, d.name))), Discharge.Auto,
        s"The branches of parallel step ${i + 1} in ${d.name.value} commute: either order gives the same result " +
          "and leaves the same world.")
    }

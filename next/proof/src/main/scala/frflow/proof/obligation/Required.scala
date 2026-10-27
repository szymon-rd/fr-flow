package frflow.proof.obligation

import cats.data.NonEmptyList
import cats.syntax.all.*
import frflow.core.analysis.{Callees, Guards, Resolved, Scope}
import frflow.core.term.interpret.Guard
import frflow.core.expr.Expr
import frflow.core.code.Code
import frflow.core.name.{DefName, NodeId, SymbolName}
import frflow.core.spec.{CallForm, Range, Written}
import frflow.core.ty.Ty
import frflow.core.vocab.SymbolType
import frflow.proof.terms.{Commutation, Keeping, Making}

/** What must hold of a node, each read off its statement, its place and the code (owner §15), in today's order:
  * `complete` (proven from its parts), `feasible`, `impl` (checked against the proven code of the Definitions it
  * mentions), `cover_<op>` (an `always` kept by each program it applies to), `commute_i`. What holds of the theory
  * as a whole (consistency, vacuity, the examples) is `Joint`'s.
  */
object Required:
  def of(r: Resolved, authored: Set[(NodeId, ObligationName)], n: NodeId): List[Obligation] =
    def how(o: ObligationName) = if authored((n, o)) then Discharge.Authored else Discharge.Auto
    complete(r, n).map(Obligation(ObligationName.Complete, _, how(ObligationName.Complete), completes(r, n))).toList ++
      feasible(r, authored, n) ++ impl(r, n) ++ commutes(r, n) ++ keeps(r, n) ++ made(r, n)

  /** `∀ U, C1 → … → Cn → N`, of a node not checked against proven code. */
  def complete(r: Resolved, n: NodeId): Option[Prop] =
    NonEmptyList.fromList(r.theory.refinement.parts(n)).filter(_ => Callees.of(r.theory, n).isEmpty).map(ps =>
      Prop.over(List(n), Prop.Implies(Hyp.parts(ps.toList), Prop.claim(n))))

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
    * (today's words). `H` is the node's parts when it has any (each a statement about what the code calls,
    * `Validate`); a leaf's is what its code relies on: the statements mentioning what the code calls
    * (`Resolved.reliesOn`).
    */
  def impl(r: Resolved, n: NodeId): List[Obligation] =
    Callees.of(r.theory, n).toList.map { c =>
      val hyps = hypotheses(r, n)
      val goal = Prop.over(Nil, Prop.Implies(Hyp.parts(hyps),
        Prop.ClaimOf(n, c.standsFor.view.mapValues(Substitute.Code(_)).toMap)))
      Obligation(ObligationName.Impl, goal, Discharge.Auto,
        s"Every result of ${c.standsFor.values.map(_.value).mkString(" and ")} meets ${n.value}" + givenWhat(hyps))
    }

  /** What `impl` of a node rests on: its parts, or for a leaf what its code relies on. */
  def hypotheses(r: Resolved, n: NodeId): List[NodeId] = r.theory.refinement.parts(n) match
    case Nil   => r.reliesOn(n)
    case parts => parts

  private def givenWhat(hyps: List[NodeId]): String =
    if hyps.isEmpty then "." else s", given what ${hyps.map(_.value).mkString(", ")} promise."

  /** `cover_<op>` of a statement of `always`, for each program it applies to whose code is proven and calls a store
    * the `always` is about (`Scope`): every run of the code keeps it, from a world meeting every `always`, on inputs
    * meeting theirs (`Keeping`), given what the code relies on. What covered code makes is asked of it by `made`.
    */
  def keeps(r: Resolved, n: NodeId): List[Obligation] =
    val guards = Guards.byAlways(r.theory)
    val stores = r.theory.node(n).flatMap(_.statement.range).toList.flatMap(Scope.models(r.theory, _)).map(_.boundary)
    val writers = Scope.of(r.theory, n).filter(op =>
      Callees.ofDefinition(r.theory, op).exists(_.calls.boundaries.exists(stores.contains)))
    (guards.toMap.get(n).toList, writers).tupled.flatMap { (kept, op) =>
      (Callees.ofDefinition(r.theory, op).flatMap(_.standsFor.get(op)), typeOf(r, op)).tupled.map { (code, ty) =>
        val goal = Prop.Keeps(n, op, Keeping.formula(op, ty, inputs(r, op, ty), kept, guards.map(_._2)),
          Map(op -> Substitute.Code(code)))
        val hyps = r.reliedOnBy(op)
        Obligation(ObligationName.Cover(op.value), Prop.over(Nil, Prop.Implies(Hyp.parts(hyps), goal)),
          Discharge.Auto, s"Every run of ${code.value} keeps ${n.value}" + givenWhat(hyps))
      }
    }

  private def typeOf(r: Resolved, op: SymbolName): Option[Ty] =
    r.theory.vocabulary.symbol(op).map(_.ty).collect { case SymbolType.Typed(t) => t }

  /** The run's inputs, named as a statement reading as its run names them, or by position. */
  private def inputs(r: Resolved, op: SymbolName, ty: Ty): List[(String, Ty)] =
    r.theory.refinement.nodes.flatMap(_.statement.call).collectFirst {
      case CallForm.Run(`op`, post, _) => post.value.params.dropRight(3).map(x => x.hint -> x.ty)
    }.getOrElse(ty match
      case Ty.FnOf(ins, _) => ins.zipWithIndex.map((t, i) => s"x$i" -> t)
      case _               => Nil)

  /** `commute_i` of each parallel step of the proven programs `n` is checked against (`Commutation`), numbered
    * across them: either order of the branches gives the same result and leaves the same world.
    */
  def commutes(r: Resolved, n: NodeId): List[Obligation] =
    val flows = Callees.of(r.theory, n).toList.flatMap(_.standsFor.keys).flatMap(op =>
      r.theory.code.attached.get(op).map(_.code).collect { case Code.ProvenFlow(f) => f })
    flows.distinct.flatMap(r.theory.vocabulary.define).flatMap(d => Commutation.of(r.theory.vocabulary, d).map(c =>
      (d, c))).zipWithIndex.map { case ((d, c), i) =>
      Obligation(ObligationName.Commute(i),
        Prop.over(Nil, Prop.Commutes(c, Callees.calledBy(r.theory, d.name))), Discharge.Auto,
        s"The branches of parallel step ${i + 1} in ${d.name.value} commute: either order gives the same result " +
          "and leaves the same world.")
    }

  /** `made_<maker>` of an `always[T]` (owner §13: the soundness of assuming it of every value), for each maker FrFlow
    * covers whose result is a `T` or a list of them: a Definition whose proven code is a define, and a store's
    * operation on its model (`Scope.modelMakers`). Every result meets the rule, the inputs meeting what always holds
    * of their types and the world every `always` about it (`Making`), given what the code relies on.
    */
  def made(r: Resolved, n: NodeId): List[Obligation] =
    val guards = Guards.byAlways(r.theory)
    (guards.toMap.get(n), r.theory.node(n).flatMap(_.statement.range)).tupled.toList.flatMap {
      case (kept, range @ Range.Made(ty)) =>
        val g = (kept, guards.map(_._2))
        byDefines(r, n, ty, g) ++ byPrograms(r, n, ty, g) ++ byModels(r, n, range, g)
      case _ => Nil
    }

  private type Guarding = (Guard, List[Guard])
  private def makes(n: NodeId, op: SymbolName, code: DefName, f: Written[Expr]): Prop.Makes =
    Prop.Makes(n, op, f, Map(op -> Substitute.Code(code)))

  private def byDefines(r: Resolved, n: NodeId, ty: Ty, g: Guarding): List[Obligation] =
    defines(r, n, ty).map((op, code, fn) => relying(r, makes(n, op, code, Making.ofDefine(op, fn, g._1, g._2)),
      s"Every result of ${code.value} meets ${n.value}"))

  private def byPrograms(r: Resolved, n: NodeId, ty: Ty, g: Guarding): List[Obligation] =
    programs(r, n, ty).map((op, code, fn) => relying(r, makes(n, op, code,
      Making.ofProgram(op, fn, inputs(r, op, fn), g._1, g._2)),
      s"Every result of a run of ${code.value} meets ${n.value}"))

  private def byModels(r: Resolved, n: NodeId, range: Range, g: Guarding): List[Obligation] =
    Scope.modelMakers(r.theory, range).map { (m, sig) =>
      val code = DefName(s"${m.name.value.capitalize}.${sig.name.value}_of")
      Obligation(ObligationName.Made(sig.name.value), Prop.over(Nil, makes(n, SymbolName(sig.name.value), code,
        Making.ofModel(m, sig, g._1, g._2))), Discharge.Auto,
        s"Every result of ${m.name.value}'s ${sig.name.value} meets ${n.value}, on a world meeting what always holds.")
    }

  /** `made_<maker>` of a maker's code, given what the code relies on. */
  private def relying(r: Resolved, goal: Prop.Makes, says: String): Obligation =
    val hyps = r.reliedOnBy(goal.maker)
    Obligation(ObligationName.Made(goal.maker.value), Prop.over(Nil, Prop.Implies(Hyp.parts(hyps), goal)),
      Discharge.Auto, says + givenWhat(hyps))

  /** The Definitions in `n`'s scope whose proven code is a define returning a `ty` or a list of them. */
  private def defines(r: Resolved, n: NodeId, ty: Ty): List[(SymbolName, DefName, Ty)] =
    Scope.of(r.theory, n).flatMap(op => (r.theory.code.attached.get(op).map(_.code), typeOf(r, op)).tupled.collect {
      case (Code.Proven(d), fn) if Guards.applies(r.theory, ty, Ty.resultOf(fn)) => (op, d, fn)
    })

  /** The Definitions in `n`'s scope whose proven code is a program whose run gives a `ty` or a list of them: each
    * with its run on the models (`f_run`).
    */
  private def programs(r: Resolved, n: NodeId, ty: Ty): List[(SymbolName, DefName, Ty)] =
    Scope.of(r.theory, n).flatMap(op => (r.theory.code.attached.get(op).map(_.code), typeOf(r, op)).tupled.collect {
      case (Code.ProvenFlow(f), fn) if (Ty.resultOf(fn) match
            case Ty.FlowOf(res) => Guards.applies(r.theory, ty, res)
            case _              => false) => (op, DefName(s"${f.value}_run"), fn)
    })

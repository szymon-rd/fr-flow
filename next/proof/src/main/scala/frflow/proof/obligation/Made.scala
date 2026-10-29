package frflow.proof.obligation

import cats.syntax.all.*
import frflow.core.analysis.{Callees, Resolved, Scope}
import frflow.core.term.interpret.Guard
import frflow.core.expr.Expr
import frflow.core.code.Code
import frflow.core.name.{DefName, NodeId, SymbolName}
import frflow.core.spec.{Range, Written}
import frflow.core.ty.Ty
import frflow.proof.terms.{CallingCode, Making}
import frflow.core.analysis.outside.{Guards, Reads}

/** What always holds kept by what covered code makes (owner §13, §37): `made_<maker>` of each maker, and
  * `made_<code>_call_<i>` at each call of plain Scala, of a statement of `always[T]`.
  */
object Made:
  /** `made_<maker>` of an `always[T]` (owner §13: the soundness of assuming it of every value), for each maker FrFlow
    * covers whose result is a `T` or a list of them: a Definition whose proven code is a define, and a store's
    * operation on its model (`Scope.modelMakers`). Every result meets the rule, the inputs meeting what always holds
    * of their types and the world every `always` about it (`Making`), given what the code relies on.
    */
  def of(r: Resolved, n: NodeId): List[Obligation] =
    val guards = Guards.byAlways(r.theory)
    (guards.toMap.get(n), r.theory.node(n).flatMap(_.statement.range)).tupled.toList.flatMap {
      case (kept, range @ Range.Made(ty)) =>
        byDefines(r, n, ty, (kept, guards.map(_._2))) ++ byPrograms(r, n, ty, (kept, guards.map(_._2))) ++
          byModels(r, n, range, kept)
      case _ => Nil
    }

  /** `made_<code>_call_<i>` of an `always[T]` (owner §37): of each proven define or program calling a Definition given
    * plain Scala, at call `i` (numbered across its calls of plain Scala), the rule of each argument it reaches, on
    * every path to the call (`CallingCode`), given what the code relies on. Asked at every call, never left to
    * `cover_`.
    */
  def atCalls(r: Resolved, n: NodeId): List[Obligation] =
    val guards = Guards.byAlways(r.theory)
    (guards.toMap.get(n), r.theory.node(n).flatMap(_.statement.range)).tupled.toList.flatMap {
      case (kept, Range.Made(ty)) => CallingCode.of(r.theory).flatMap(c => c.calls.zipWithIndex.collect {
          case (tys, i) if tys.exists(Guards.applies(r.theory, ty, _)) =>
            val at = s"${c.code.value}_call_$i"
            val hyps = r.reliedOnBy(c.definition)
            Obligation(ObligationName.Made(at), Prop.over(Nil, Prop.Implies(Hyp.parts(hyps) ++
              madeBy(r, n, ty, (kept, guards.map(_._2)), c.definition), Prop.Makes(n, SymbolName(at),
                c.formula(i, kept), Map.empty))), Discharge.Auto,
              s"What ${c.code.value} hands plain Scala at call ${i + 1} meets ${n.value}" +
                Required.givenWhat(hyps))
        })
      case _                      => Nil
    }

  /** What the Definitions `op`'s proven code calls make meets the rule too, each known by its claims: their own
    * `made_<maker>` (`m_<maker>`, each proven of its own code), so a value one of them returns is known to meet it
    * where the code hands it on.
    */
  private def madeBy(r: Resolved, n: NodeId, ty: Ty, g: Guarding, op: SymbolName): List[Hyp] =
    val called = Callees.ofDefinition(r.theory, op).toList.flatMap(_.calls.symbols).toSet - op
    defines(r, n, ty).filter((callee, _, _) => called(callee)).map((callee, _, fn) =>
      Hyp(s"m_${callee.value}", Prop.Makes(n, callee, Making.ofDefine(callee, fn, g._1, g._2), Map.empty)))

  private type Guarding = (Guard, List[Guard])
  private def makes(n: NodeId, op: SymbolName, code: DefName, f: Written[Expr]): Prop.Makes =
    Prop.Makes(n, op, f, Map(op -> Substitute.Code(code)))

  private def byDefines(r: Resolved, n: NodeId, ty: Ty, g: Guarding): List[Obligation] =
    defines(r, n, ty).map((op, code, fn) => relying(r, makes(n, op, code, Making.ofDefine(op, fn, g._1, g._2)),
      madeBy(r, n, ty, g, op), s"Every result of ${code.value} meets ${n.value}"))

  /** A run's world takes the rules of the stores the program calls only (owner §33). */
  private def byPrograms(r: Resolved, n: NodeId, ty: Ty, g: Guarding): List[Obligation] =
    programs(r, n, ty).map((op, code, fn) => relying(r, makes(n, op, code,
      Making.ofProgram(op, fn, Required.inputs(r, op, fn), g._1,
        Guards.reading(r.theory, Reads.ofProgram(r.theory, op))
        .map(_._2))), madeBy(r, n, ty, g, op), s"Every result of a run of ${code.value} meets ${n.value}"))

  private def byModels(r: Resolved, n: NodeId, range: Range, kept: Guard): List[Obligation] =
    Scope.modelMakers(r.theory, range).map { (m, sig) =>
      val code = DefName(s"${m.name.value.capitalize}.${sig.name.value}_of")
      val within = Guards.reading(r.theory, List(m.name)).map(_._2)
      Obligation(ObligationName.Made(sig.name.value), Prop.over(Nil, makes(n, SymbolName(sig.name.value), code,
        Making.ofModel(m, sig, kept, within))), Discharge.Auto,
        s"Every result of ${m.name.value}'s ${sig.name.value} meets ${n.value}, on a world meeting what always holds.")
    }

  /** `made_<maker>` of a maker's code, given what the code relies on and what its callees make (`madeBy`). */
  private def relying(r: Resolved, goal: Prop.Makes, made: List[Hyp], says: String): Obligation =
    val hyps = r.reliedOnBy(goal.maker)
    Obligation(ObligationName.Made(goal.maker.value), Prop.over(Nil, Prop.Implies(Hyp.parts(hyps) ++ made, goal)),
      Discharge.Auto, says + Required.givenWhat(hyps))

  /** The Definitions in `n`'s scope whose proven code is a define returning a `ty` or a list of them. */
  private def defines(r: Resolved, n: NodeId, ty: Ty): List[(SymbolName, DefName, Ty)] =
    Scope.of(r.theory, n).flatMap(op =>
      (r.theory.code.attached.get(op).map(_.code), Required.typeOf(r, op)).tupled.collect {
      case (Code.Proven(d), fn) if Guards.applies(r.theory, ty, Ty.resultOf(fn)) => (op, d, fn)
    })

  /** The Definitions in `n`'s scope whose proven code is a program whose run gives a `ty` or a list of them: each
    * with its run on the models (`f_run`).
    */
  private def programs(r: Resolved, n: NodeId, ty: Ty): List[(SymbolName, DefName, Ty)] =
    Scope.of(r.theory, n).flatMap(op =>
      (r.theory.code.attached.get(op).map(_.code), Required.typeOf(r, op)).tupled.collect {
      case (Code.ProvenFlow(f), fn) if (Ty.resultOf(fn) match
            case Ty.FlowOf(res, _) => Guards.applies(r.theory, ty, res)
            case _                 => false) => (op, DefName(s"${f.value}_run"), fn)
    })

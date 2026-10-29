package frflow.proof.lean.lower

import frflow.core.name.SymbolName
import frflow.proof.lean.ast.*
import frflow.proof.lean.term.Printed
import frflow.proof.obligation.{Obligation, Prop, Supplied}

/** An obligation FrFlow met with the witnesses it derived, as its theorem: `theorem consistent_0 : Obl.consistent_0
  * :=\n  fun grants => ⟨w₁, …, by frflow_witness⟩` (the values provided taken first; every witness printed by the one
  * printer of terms, or as a constant), the proof left to FrFlow's own tactic.
  */
final class LowerWitness(env: LowerEnv, naming: Naming, props: LowerProp):
  def apply(o: Obligation, by: List[Supplied]): Decl =
    val name = LowerObligation.name(o.name)
    val met = LExpr.Anonymous(ordered(o.goal, by) :+ LExpr.By(Names.builtin("frflow_witness")))
    Decl.Theorem(Nil, name, Nil, LExpr.Const(List(Names.builtin("Obl"), name)), Proof.Below(provided(o.goal, met)),
      Break.SameLine)

  /** `fun grants sessions _ => met`, for a statement for every value provided: what always holds of them taken too,
    * and what the assumptions about them alone say.
    */
  private def provided(goal: Prop, met: LExpr): LExpr = goal match
    case Prop.ForEvery(Nil, _)   => met
    case Prop.ForEvery(ss, body) => LExpr.Fun(ss.map(s => LBinder.Bare(Names.ident(s.value))) ++
        (props.fromOutsideOf(ss) ++ premises(body)).map(_ => LBinder.Bare(Names.builtin("_"))), met)
    case _                       => met

  private def premises(body: Prop): List[Prop] = body match
    case Prop.Implies(hs, _) => hs.map(_.prop)
    case _                   => Nil

  /** Each witness printed in the order solved, every one given before standing for its value in it (R14.6); then in
    * the order the statement binds them.
    */
  private def ordered(goal: Prop, by: List[Supplied]): List[LExpr] =
    val printed = by.foldLeft((Map.empty[SymbolName, LExpr], List.empty[(Option[SymbolName], LExpr)])) {
      case ((known, out), Supplied.Term(t, s)) =>
        val e = Printed.standing(env, naming, 0, known)(t)
        (known + (s -> e), out :+ (Some(s) -> e))
      case ((known, out), Supplied.Value(c))   =>
        (known, out :+ (None -> LowerValue(env)(c.value, c.ty).runA(naming).value))
      case ((known, out), Supplied.Code(s, d)) => (known + (s -> props.code(d, known)), out)
    }._2
    bound(goal).filter(ss => printed.forall(_._1.isDefined) && ss.toSet == printed.flatMap(_._1).toSet)
      .fold(printed.map(_._2))(ss => ss.flatMap(s => printed.collectFirst { case (Some(`s`), e) => e }))

  /** The values the statement binds by `∃`, in order. */
  private def bound(p: Prop): Option[List[SymbolName]] = p match
    case Prop.ForEvery(_, body) => bound(body)
    case Prop.Implies(_, body)  => bound(body)
    case Prop.ForSome(ss, _)    => Some(ss)
    case _                      => None

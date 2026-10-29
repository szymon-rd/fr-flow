package frflow.proof.audit

import cats.data.ValidatedNec
import frflow.core.analysis.Resolved
import frflow.core.expr.{Binder, Expr}
import frflow.core.name.VarId
import frflow.core.spec.Written
import frflow.core.term.interpret.ToExpr
import frflow.core.ty.Ty
import frflow.core.typing.{IrCheck, IrError}
import frflow.core.vocab.SymbolType
import frflow.proof.obligation.{Discharge, Obligation, ObligationName, Prop, Supplied}

/** The terms the compiler builds into obligations, checked as elaboration's are (`IrCheck`, over the theory's
  * vocabulary): the guards, the `keeps_` and `makes_` formulas of `cover_` and `made_` (`Keeping`, `Making`, at a call
  * `CallingCode`), the conditions and formulas of the whole theory's (`Conditions`), a store's start under its guard,
  * and the values a witness supplies (`Defining`). A commutation's two orders are lowered from the program's own
  * steps, which `IrCheck.theory` checks.
  */
object WellFormed:
  def of(r: Resolved, obligations: List[Obligation]): List[(ObligationName, IrError)] =
    val check = IrCheck.of(r.theory.vocabulary)
    def all(v: ValidatedNec[IrError, Ty]) = v.fold(_.iterator.toList, _ => Nil)
    def typed(v: ValidatedNec[IrError, Ty], at: Ty, e: Expr) =
      all(v) ++ v.toOption.filter(uncurried(_) != uncurried(at)).map(_ => IrError.Mistyped(e))
    obligations.flatMap { o =>
      val formulas = terms(o.goal).flatMap {
        case Left(w)              => typed(check(w.value), Ty.Bool, w.value)
        case Right((state, rule)) =>
          val e = ToExpr.of(rule, 1)
          typed(check(e, List(Binder(VarId.level(0), "s", state))), Ty.Bool, e)
      }
      val supplied = o.discharge match
        case Discharge.Witnessed(by) => by.collect { case Supplied.Term(t, of) => (ToExpr.of(t.run), of) }.flatMap(
            (e, of) => r.theory.vocabulary.symbol(of).map(_.ty).collect { case SymbolType.Typed(at) =>
              typed(check(e), at, e) }.getOrElse(all(check(e))))
        case _                       => Nil
      (formulas ++ supplied).map(o.name -> _)
    }

  /** A function of several inputs, however it takes them (a witness is a `fun` per input). */
  private def uncurried(t: Ty): Ty = t match
    case Ty.FnOf(as, r) => uncurried(r) match
        case Ty.FnOf(bs, s) => Ty.FnOf(as ++ bs, s)
        case s              => Ty.FnOf(as, s)
    case other          => other

  /** The formulas a statement holds, and each start's rule under its guard (over the state, at level 0). */
  private def terms(p: Prop): List[Either[Written[Expr], (Ty, frflow.core.term.Final[Boolean])]] = p match
    case Prop.Keeps(_, _, f, _)          => List(Left(f))
    case Prop.Makes(_, _, f, _)          => List(Left(f))
    case Prop.Formula(w, _)              => List(Left(w))
    case Prop.Starts(_, _, state, guard) => guard.map(g => Right(state -> g)).toList
    case Prop.Implies(hs, c)             => hs.flatMap(h => terms(h.prop)) ++ terms(c)
    case Prop.Iff(a, b)                  => terms(a) ++ terms(b)
    case Prop.Both(ps)                   => ps.toList.flatMap(terms)
    case Prop.Not(a)                     => terms(a)
    case Prop.Forall(_, b)               => terms(b)
    case Prop.Exists(_, b)               => terms(b)
    case Prop.ForEvery(_, b)             => terms(b)
    case Prop.ForSome(_, b)              => terms(b)
    case _                               => Nil

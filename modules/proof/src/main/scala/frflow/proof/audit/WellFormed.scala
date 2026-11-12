package frflow.proof.audit

import cats.data.ValidatedNec
import frflow.core.analysis.resolution.Resolved
import frflow.core.expr.Expr
import frflow.core.spec.Written
import frflow.core.term.interpret.ToExpr
import frflow.core.ty.Ty
import frflow.core.typing.{IrCheck, IrError}
import frflow.core.vocab.SymbolType
import frflow.proof.obligation.{Discharge, Obligation, ObligationName, Prop, Supplied}

/** The terms the compiler builds into obligations, checked as elaboration's are (`IrCheck`, over the theory's
  * vocabulary): the guards, the `makes_` formulas of `made_` (`Making`, at a call `CallingCode`), the conditions and
  * formulas of the whole theory's (`Conditions`), and the values a witness supplies (`Defining`).
  */
object WellFormed:
  def of(r: Resolved, obligations: List[Obligation]): List[(ObligationName, IrError)] =
    val check = IrCheck.of(r.theory.vocabulary)
    def all(v: ValidatedNec[IrError, Ty]) = v.fold(_.iterator.toList, _ => Nil)
    def typed(v: ValidatedNec[IrError, Ty], at: Ty, e: Expr) =
      all(v) ++ v.toOption.filter(uncurried(_) != uncurried(at)).map(_ => IrError.Mistyped(e))
    obligations.flatMap { o =>
      val formulas = terms(o.goal).flatMap(w => typed(check(w.value), Ty.Bool, w.value))
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

  /** The formulas a statement holds. */
  private def terms(p: Prop): List[Written[Expr]] = p match
    case Prop.Makes(_, _, f, _) => List(f)
    case Prop.Formula(w, _)     => List(w)
    case Prop.Implies(hs, c)    => hs.flatMap(h => terms(h.prop)) ++ terms(c)
    case Prop.Iff(a, b)         => terms(a) ++ terms(b)
    case Prop.Both(ps)          => ps.toList.flatMap(terms)
    case Prop.Not(a)            => terms(a)
    case Prop.Forall(_, b)      => terms(b)
    case Prop.Exists(_, b)      => terms(b)
    case Prop.ForEvery(_, b)    => terms(b)
    case Prop.ForSome(_, b)     => terms(b)
    case _                      => Nil

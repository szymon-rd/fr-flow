package frflow.proof.lean.lower

import frflow.core.ty.Ty
import frflow.proof.lean.ast.*

/** A type's Lean (`(List Grant)`, `(String → Option UserId)`, `(CrmStore × World)`), as today's `Types.tpe`: every
  * compound type in parentheses; a program's, its run from a world (`(World → ((Except E R) × World))` where it may
  * fail with `E`). A declaration's type is its parameters' types and its result's, joined by `→`.
  */
object LowerType:
  import Atoms.{const, name}
  import LExpr.{App, Infix, Paren}
  private def chain(op: LOp, ts: List[LExpr]): LExpr = ts.reduceRight(Infix(op, _, _))

  def apply(t: Ty): LExpr = t match
    case Ty.Bool             => name("Prop")
    case Ty.Num(_)           => name("Int")
    case Ty.Str              => name("String")
    case Ty.Unit             => name("Unit")
    case Ty.World            => name("World")
    case Ty.Never            => throw IllegalStateException("FrFlow bug: the type of a step that only raises, lowered")
    case Ty.MapOf(k, v)      => Paren(Infix(LOp.Arrow, apply(k), App(name("Option"), List(apply(v)))))
    case Ty.SetOf(a)         => Paren(Infix(LOp.Arrow, apply(a), name("Prop")))
    case Ty.ListOf(a)        => Paren(App(name("List"), List(apply(a))))
    case Ty.OptionOf(a)      => Paren(App(name("Option"), List(apply(a))))
    case Ty.EitherOf(e, a)   => Paren(App(name("Except"), List(apply(e), apply(a))))
    case Ty.TupleOf(as)      => Paren(chain(LOp.Times, as.map(apply)))
    case Ty.FnOf(as, r)      => Paren(chain(LOp.Arrow, (as :+ r).map(apply)))
    case Ty.Sort(n)          => const(n.value)
    case Ty.Data(n)          => const(n.value)
    case Ty.FlowOf(r, e)     =>
      val outcome = e.fold(r)(Ty.EitherOf(_, r))
      Paren(Infix(LOp.Arrow, name("World"), Paren(chain(LOp.Times, List(apply(outcome), name("World"))))))

  /** A binder's type: a function's arrows unparenthesized at the top (`(expire : CrmStore → Int → CrmStore)`). */
  def binder(t: Ty): LExpr = t match
    case Ty.FnOf(as, r) => declaration(as, apply(r))
    case other          => apply(other)

  /** `A → B → R`: a declaration's type, unparenthesized at the top. */
  def declaration(params: List[Ty], result: LExpr): LExpr = chain(LOp.Arrow, params.map(apply) :+ result)

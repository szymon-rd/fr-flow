package frflow.proof.lean.lower

import cats.syntax.all.*
import frflow.core.name.{CtorName, DefName, TypeName}
import frflow.core.ty.Ty
import frflow.proof.lean.ast.{LBinder, LExpr, LeanName, Names}

/** The Lean the lowering spells itself: a name (`some`, `pure`, `Int`), a dotted constant (`List.filter`), a call,
  * a define's head and a constructor.
  */
object Atoms:
  def name(s: String): LExpr = LExpr.Name(Names.builtin(s))
  def const(dotted: String): LExpr = LExpr.Const(dotted.split('.').toList.map(Names.builtin))
  /** `(f a b)`: an application in parentheses, as every call is generated. */
  def call(f: LExpr, args: List[LExpr]): LExpr = LExpr.Paren(LExpr.App(f, args))

  /** `K.d`, or `(K.d t1 … tk)` applied to the open terms the define is over. */
  def define(env: LowerEnv, d: DefName): LExpr = define(env, d, _ => None)

  /** The same, each open term written as what stands for it, if anything does (`standing`). */
  def define(env: LowerEnv, d: DefName, standing: LeanName => Option[LExpr]): LExpr =
    val c = LExpr.Const(List(Names.builtin(env.kb.value), Names.define(env.calls(d).value)))
    env.openTerms(d) match
      case Nil   => c
      case terms => call(c, terms.map(t => standing(t).getOrElse(LExpr.Name(t))))

  /** `Event.Expired`, `Booking.mk`: a constructor, qualified by its type. */
  def ctor(d: TypeName, c: CtorName): LExpr = LExpr.Ctor(Names.ident(d.value), Names.ident(c.value))

  /** `fun (x0 : A) (x1 : B) => []`: a Definition doing nothing (`Substitute.canDoNothing` holds of its type). */
  def nothing(naming: Naming, t: Ty): LExpr = t match
    case Ty.FnOf(ins, r) =>
      val xs = ins.indices.toList.traverse(i => Naming.helper(s"x$i", Set.empty)).runA(naming).value
      LExpr.Paren(LExpr.Fun(xs.zip(ins).map((x, ty) => LBinder.Explicit(x, LowerType(ty))), nothingOf(r, ins, xs)))
    case _ => throw IllegalStateException("FrFlow bug: doing nothing for a Definition that is not a function")

  /** `False`, `[]`, `none`, or the first input of the result's type, returned unchanged. */
  private def nothingOf(r: Ty, ins: List[Ty], xs: List[LeanName]): LExpr = r match
    case Ty.Bool        => name("False")
    case Ty.ListOf(_)   => LExpr.ListLit(Nil)
    case Ty.OptionOf(_) => name("none")
    case other          => xs.zip(ins).collectFirst { case (x, `other`) => LExpr.Name(x) }
      .getOrElse(throw IllegalStateException("FrFlow bug: no input to return unchanged"))

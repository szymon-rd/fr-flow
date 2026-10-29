package frflow.proof.lean.lower

import frflow.core.name.{CtorName, DefName, TypeName}
import frflow.proof.lean.ast.{LExpr, LeanName, Names}

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
    val c = LExpr.Const(List(Names.builtin(env.kb.value), Names.define(d.value)))
    env.openTerms(d) match
      case Nil   => c
      case terms => call(c, terms.map(t => standing(t).getOrElse(LExpr.Name(t))))

  /** `Event.Expired`, `Booking.mk`: a constructor, qualified by its type. */
  def ctor(d: TypeName, c: CtorName): LExpr = const(s"${d.value}.${c.value}")

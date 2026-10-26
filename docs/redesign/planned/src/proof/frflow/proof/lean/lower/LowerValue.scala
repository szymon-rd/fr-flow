package frflow.proof.lean.lower

import cats.data.State
import cats.syntax.all.*
import frflow.core.expr.Value
import frflow.core.name.{CtorName, TypeName}
import frflow.core.ty.Ty
import frflow.proof.lean.ast.*

/** A constant as Lean writes it: the same Lean as the value written in a model (today's `LeanPrinter.value`). */
final class LowerValue(env: LowerEnv):
  import Atoms.{call, name}
  private type L[A] = State[Naming, A]

  def apply(v: Value, t: Ty): L[LExpr] = (v, t) match
    case (Value.Bool(b), _)                     => State.pure(name(if b then "True" else "False"))
    case (Value.Num(n), _)                      => State.pure(if n < 0 then LExpr.Paren(LExpr.Num(n)) else LExpr.Num(n))
    case (Value.Str(s), _)                      => State.pure(LExpr.Str(s))
    case (Value.Unit, _)                        => State.pure(name("()"))
    case (Value.Many(xs), Ty.ListOf(a))         => xs.traverse(apply(_, a)).map(LExpr.ListLit(_))
    case (Value.Maybe(None), _)                 => State.pure(name("none"))
    case (Value.Maybe(Some(x)), Ty.OptionOf(a)) => apply(x, a).map(y => call(name("some"), List(y)))
    case (Value.Data(c, fs), Ty.Data(d))        => data(d, c, fs)
    case _                                      => ??? // tuples, outcomes, maps and sets (with their helper), worlds

  /** A constructor applied to its fields; a case of an enum without fields alone. */
  private def data(d: TypeName, c: CtorName, fs: List[Value]): L[LExpr] =
    val head = Lower.ctor(d, c)
    val decl = env.data(d)
    if fs.isEmpty && decl.exists(_.isEnum) then State.pure(head)
    else fs.zip(decl.toList.flatMap(_.fieldsOf(c))).traverse(apply(_, _)).map(call(head, _))

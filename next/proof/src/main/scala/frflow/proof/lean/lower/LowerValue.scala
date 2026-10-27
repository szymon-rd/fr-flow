package frflow.proof.lean.lower

import cats.data.State
import cats.syntax.all.*
import frflow.core.expr.{Side, Value}
import frflow.core.name.{CtorName, ModelName, TypeName}
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
    case (Value.Inject(side, x), Ty.EitherOf(l, r)) =>
      val (ctor, ty) = if side == Side.Error then ("Except.error", l) else ("Except.ok", r)
      apply(x, ty).map(y => call(Atoms.const(ctor), List(y)))
    case (Value.Tuple(xs), Ty.TupleOf(ts))      => xs.zip(ts).traverse(apply(_, _)).map(LExpr.Tuple(_))
    case (Value.Pairs(es), Ty.MapOf(k, v))      => map(es, k, v)
    case (Value.Many(xs), Ty.SetOf(a))          => set(xs, a)
    case (Value.World(states, fs), Ty.World)    => world(states, fs)
    case (other, ty)                            =>
      throw IllegalStateException(s"FrFlow bug: the value $other is not one of type $ty")

  /** `(World.mk s₁ …)`: each model's state, at its type, then its faults where a boundary may fail. */
  private def world(states: List[(ModelName, Value)], faults: List[Boolean]): L[LExpr] =
    states.traverse((m, v) => apply(v, env.modelState(m).getOrElse(
      throw IllegalStateException(s"FrFlow bug: a world's state of ${m.value}, a model the theory has not")))
    ).map(ss => call(Atoms.const("World.mk"), ss ++ Option.when(env.faulty)(LExpr.Typed(
      LExpr.ListLit(faults.map(f => name(if f then "true" else "false"))), LowerFaults.listOfBool))))

  /** `(fun k => if k = k₁ then some v₁ else … none)`: a map as the function Lean's `K → Option V` is. */
  private def map(es: List[(Value, Value)], k: Ty, v: Ty): L[LExpr] =
    for
      pairs <- es.traverse((a, b) => (apply(a, k), apply(b, v)).tupled)
      x     <- Naming.helper("k", pairs.flatMap((a, b) => LExprs.identifiers(a) ++ LExprs.identifiers(b)).toSet)
    yield
      val body = pairs.foldRight(name("none"))((p, rest) =>
        LExpr.If(LExpr.Infix(LOp.Eq, LExpr.Name(x), p._1), call(name("some"), List(p._2)), rest))
      LExpr.Paren(LExpr.Fun(List(LBinder.Bare(x)), body))

  /** `(fun x => x = a₁ ∨ …)`, or `(fun x => False)`: a set as the predicate Lean's `A → Prop` is. */
  private def set(xs: List[Value], a: Ty): L[LExpr] =
    for
      elems <- xs.traverse(apply(_, a))
      x     <- Naming.helper("x", elems.flatMap(LExprs.identifiers).toSet)
    yield
      val body = elems.map(e => LExpr.Infix(LOp.Eq, LExpr.Name(x), e): LExpr)
        .reduceRightOption(LExpr.Infix(LOp.Or, _, _)).getOrElse(name("False"))
      LExpr.Paren(LExpr.Fun(List(LBinder.Bare(x)), body))

  /** A constructor applied to its fields; a case of an enum without fields alone. */
  private def data(d: TypeName, c: CtorName, fs: List[Value]): L[LExpr] =
    val head = Atoms.ctor(d, c)
    val decl = env.data(d).getOrElse(throw IllegalStateException(s"FrFlow bug: a value of ${d.value}, not a type"))
    val types = decl.fieldsOf(c)
    if fs.size != types.size then throw IllegalStateException(s"FrFlow bug: ${c.value} given ${fs.size} fields")
    else if fs.isEmpty && decl.isEnum then State.pure(head)
    else fs.zip(types).traverse(apply(_, _)).map(call(head, _))

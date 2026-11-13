package frflow.proof.prover.lower

import cats.data.State
import cats.syntax.all.*
import frflow.core.expr.{Side, Value}
import frflow.core.name.{CtorName, TypeName}
import frflow.core.ty.Ty
import frflow.proof.prover.ast.*

/** A constant as the prover is given it, written into any syntax: the same text as the value written in a model. */
final class LowerValue[E](env: LowerEnv)(using syntax: Syntax[E], seen: Seen[E]):
  private val atoms = new Atoms(syntax)
  import atoms.{call, name}
  private type L[A] = State[Naming, A]

  def apply(v: Value, t: Ty): L[E] = (v, t) match
    case (Value.Bool(b), _)                     => State.pure(name(if b then "True" else "False"))
    case (Value.Num(n), _)                      =>
      State.pure(if n < 0 then syntax.paren(syntax.num(n)) else syntax.num(n))
    case (Value.Str(s), _)                      => State.pure(syntax.str(s))
    case (Value.Unit, _)                        => State.pure(name("()"))
    case (Value.Many(xs), Ty.ListOf(a))         => xs.traverse(apply(_, a)).map(syntax.listLit(_))
    case (Value.Maybe(None), _)                 => State.pure(name("none"))
    case (Value.Maybe(Some(x)), Ty.OptionOf(a)) => apply(x, a).map(y => call(name("some"), List(y)))
    case (Value.Data(c, fs), Ty.Data(d))        => data(d, c, fs)
    case (Value.Inject(side, x), Ty.EitherOf(l, r)) =>
      val (ctor, ty) = if side == Side.Error then ("Except.error", l) else ("Except.ok", r)
      apply(x, ty).map(y => call(atoms.const(ctor), List(y)))
    case (Value.Tuple(xs), Ty.TupleOf(ts))      => xs.zip(ts).traverse(apply(_, _)).map(syntax.tuple(_))
    case (Value.Pairs(es), Ty.MapOf(k, v))      => map(es, k, v)
    case (Value.Many(xs), Ty.SetOf(a))          => set(xs, a)
    case (other, ty)                            =>
      throw IllegalStateException(s"FrFlow bug: the value $other is not one of type $ty")

  /** `(fun k => if k = k₁ then some v₁ else … none)`: a map as the function Lean's `K → Option V` is. */
  private def map(es: List[(Value, Value)], k: Ty, v: Ty): L[E] =
    for
      pairs <- es.traverse((a, b) => (apply(a, k), apply(b, v)).tupled)
      x     <- Naming.helper("k", pairs.flatMap((a, b) => seen.names(a) ++ seen.names(b)).toSet)
    yield
      val body = pairs.foldRight(name("none"))((p, rest) =>
        syntax.cond(syntax.infix(LOp.Eq, syntax.name(x), p._1), call(name("some"), List(p._2)), rest))
      syntax.paren(syntax.fun(List(Binding.Bare(x)), body))

  /** `(fun x => x = a₁ ∨ …)`, or `(fun x => False)`: a set as the predicate Lean's `A → Prop` is. */
  private def set(xs: List[Value], a: Ty): L[E] =
    for
      elems <- xs.traverse(apply(_, a))
      x     <- Naming.helper("x", elems.flatMap(seen.names).toSet)
    yield
      val body = elems.map(e => syntax.infix(LOp.Eq, syntax.name(x), e))
        .reduceRightOption(syntax.infix(LOp.Or, _, _)).getOrElse(name("False"))
      syntax.paren(syntax.fun(List(Binding.Bare(x)), body))

  /** A constructor applied to its fields; a case of an enum without fields alone. */
  private def data(d: TypeName, c: CtorName, fs: List[Value]): L[E] =
    val head = atoms.ctor(d, c)
    val decl = env.data(d).getOrElse(throw IllegalStateException(s"FrFlow bug: a value of ${d.value}, not a type"))
    val types = decl.fieldsOf(c)
    if fs.size != types.size then throw IllegalStateException(s"FrFlow bug: ${c.value} given ${fs.size} fields")
    else if fs.isEmpty && decl.isEnum then State.pure(head)
    else fs.zip(types).traverse(apply(_, _)).map(call(head, _))

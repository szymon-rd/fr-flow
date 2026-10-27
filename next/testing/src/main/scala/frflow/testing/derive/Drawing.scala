package frflow.testing.derive

import cats.data.StateT
import cats.syntax.all.*
import frflow.core.code.Values
import frflow.core.example.Gen
import frflow.core.expr.{Side, Value}
import frflow.core.name.CtorName
import frflow.core.ty.{DataType, Ty}
import frflow.eval.{Env, Fn, Races, ScalaValue}
import frflow.testing.derive.Rolls.*

/** One case's draws at its size, from where its draws start (`Draws`: the values drawn, the stream): `Gen`
  * interpreted, and the derived value of each type, as data. Each value of a type `T` inside the one drawn (a list's
  * element, a record's field, …: the shapes `Guards` walks) is drawn again, up to `Derive.Tries` times, until every
  * `always[T]` holds of it, so the whole meets what always holds of every type it holds. Below `Drawing.Deepest`, an
  * option is empty, a list has no element, a record takes the constructor with the fewest fields.
  */
private[derive] final class Drawing(d: Derive, size: Int):
  def gen[A](g: Gen[A]): D[A] = g match
    case Gen.Derived(ty)       => value(ty, 0).map(v => Fn.as[A](d.semantics.literal(v, ty)))
    case Gen.Const(a)          => pure(a)
    case Gen.OneOf(as)         => pick(as.toList.toVector)
    case Gen.Bind(first, next) => gen(first).flatMap(x => gen(next(x)))
    case Gen.Described(h, _)   => gen(h)

  /** A value of `ty` meeting every `always` of each type it holds, kept for the case's next values of `ty`. */
  def value(ty: Ty, depth: Int): D[Value] =
    meeting(ty)(chosen(ty, depth)).flatTap(v => StateT.modify(st => st.copy(pool = st.pool.kept(ty, v))))

  /** From the generator given for the type (three times in four; derived when its value breaks a rule), an
    * example's value, one drawn before, or fresh.
    */
  private def chosen(ty: Ty, depth: Int): D[Value] =
    (chance(0.75), chance(0.15), chance(Pool.reuse(ty)), StateT.inspect[O, Draws, Vector[Value]](_.pool.of(ty))).tupled
      .flatMap((fromGiven, seeded, pooled, drawn) =>
        d.generatorFor(ty).filter(_ => fromGiven).map(g => orElse(givenBy(ty, g), fresh(ty, depth)))
          .orElse(Option.when(seeded && d.seeds.of(ty).nonEmpty)(pick(d.seeds.of(ty))))
          .orElse(Option.when(pooled && drawn.nonEmpty)(pick(drawn)))
          .getOrElse(fresh(ty, depth)))

  /** A given generator's value, as data, when it meets what always holds of every type it holds. */
  private def givenBy(ty: Ty, g: Gen[?]): D[Value] = gen(g).flatMap { a =>
    val v = d.semantics.reflect(ScalaValue(a), ty)
    if d.meets(v, ty) then pure(v) else nothing
  }

  private def meeting(ty: Ty)(draw: D[Value]): D[Value] =
    val own = d.always.made.filter(_.ty == ty)
    if own.isEmpty then draw else retried(draw, v => own.forall(_.holds(d.semantics.literal(v, ty), none)))

  private def fresh(ty: Ty, depth: Int): D[Value] = ty match
    case Ty.Bool           => chance(0.5).map(Value.Bool(_))
    case Ty.Num(_)         => number.map(Value.Num(_))
    case Ty.Str            => string.map(Value.Str(_))
    case Ty.Unit           => pure(Value.Unit)
    case Ty.ListOf(a)      => many(a, depth).map(Value.Many(_))
    case Ty.SetOf(a)       => many(a, depth).map(xs => Value.Many(xs.distinct))
    case Ty.MapOf(k, w)    => many(Ty.TupleOf(List(k, w)), depth).map(ps => Value.Pairs(ps.collect {
        case Value.Tuple(List(a, b)) => a -> b }.distinctBy(_._1)))
    case Ty.OptionOf(a)    => chance(emptier(depth)).flatMap(empty =>
        if empty then pure(Value.Maybe(None)) else value(a, depth + 1).map(x => Value.Maybe(Some(x))))
    case Ty.EitherOf(l, r) => chance(0.25).flatMap(left =>
        if left then value(l, depth + 1).map(Value.Inject(Side.Error, _))
        else value(r, depth + 1).map(Value.Inject(Side.Value, _)))
    case Ty.TupleOf(as)    => as.traverse(value(_, depth + 1)).map(Value.Tuple(_))
    case Ty.Data(n)        => d.vocabulary.dataType(n).fold(nothing[Value])(data(_, depth))
    case Ty.World          => world(depth)
    case _                 => nothing

  /** Each model's state meeting every `always(stored)` about it, the faults the failing boundaries' calls take in
    * turn and, when a program races, the races' winners (`Races`).
    */
  private def world(depth: Int): D[Value] =
    val states = d.vocabulary.models.traverse(m =>
      retried(value(m.state, depth + 1), v => d.always.keeps(m.name, d.semantics.literal(v, m.state))).map(m.name -> _))
    (states, bools(d.mayFail, 0.3), bools(d.races, 0.5)).mapN((held, faults, races) =>
      Value.World(if d.races then held :+ (Races.model -> Value.Many(races.map(Value.Bool(_)))) else held, faults))

  private def bools(wanted: Boolean, p: Double): D[List[Boolean]] =
    if !wanted then pure(Nil) else below(size + 2).flatMap(n => List.fill(n)(chance(p)).sequence)

  /** One of its constructors over drawn fields; deep down, one with the fewest fields. */
  private def data(dt: DataType, depth: Int): D[Value] =
    val ctors = dt match
      case DataType.Product(_, _, fs) => List(CtorName("mk") -> fs.map(_.ty))
      case DataType.Sum(_, _, cs)     => cs.toList.map(c => c.name -> c.fields.map(_.ty))
    val fewest = ctors.map(_._2.size).minOption.getOrElse(0)
    val from = if depth > 2 then ctors.filter(_._2.size == fewest) else ctors
    pick(from.toVector).flatMap((c, fields) => fields.traverse(value(_, depth + 1)).map(Value.Data(c, _)))

  /** Fewer elements the deeper it is; none below the deepest. */
  private def many(a: Ty, depth: Int): D[List[Value]] =
    if depth >= Drawing.Deepest then pure(Nil)
    else below(size / (depth + 1) + 2).flatMap(n => List.fill(n)(value(a, depth + 1)).sequence)

  /** How often an option is empty: more often the deeper it is, always below the deepest. */
  private def emptier(depth: Int): Double = if depth >= Drawing.Deepest then 1.0 else 0.25 + 0.15 * depth

  private def none: Env = Env.of(Values.none)

  private def number: D[BigInt] = (chance(0.3), chance(0.4)).tupled.flatMap((small, near) =>
    if small then below(3).map(k => BigInt(k - 1))
    else if near && d.seeds.numbers.nonEmpty then (pick(d.seeds.numbers), below(3)).mapN((x, k) => x + (k - 1))
    else below(20 * size + 1).map(k => BigInt(k - 10 * size)))

  private def string: D[String] = chance(0.2).flatMap(empty =>
    if empty then pure("") else below(4).flatMap(n => List.fill(n + 1)(below(3).map("ab1"(_))).sequence)
      .map(_.mkString))

private[derive] object Drawing:
  /** Below this depth a drawn value holds nothing more: options empty, lists without elements. */
  val Deepest: Int = 5

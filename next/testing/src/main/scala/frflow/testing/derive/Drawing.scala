package frflow.testing.derive

import cats.Eval
import cats.data.{OptionT, StateT}
import cats.syntax.all.*
import frflow.core.code.Values
import frflow.core.example.Gen
import frflow.core.expr.{Side, Value}
import frflow.core.name.CtorName
import frflow.core.ty.{DataType, Ty}
import frflow.eval.{Env, Fn, ScalaValue}
import java.util.SplittableRandom

/** One case's draws, from its random stream at its size, the values it has drawn kept (`Pool`): `Gen` interpreted,
  * and the derived value of each type, as data. Each value of a type `T` inside the one drawn (a list's element, a
  * record's field, …: the shapes `Guards` walks) is drawn again, up to `Derive.Tries` times, until every `always[T]`
  * holds of it, so the whole meets what always holds of every type it holds.
  */
private[derive] final class Drawing(d: Derive, random: SplittableRandom, size: Int):
  private type O[A] = OptionT[Eval, A]
  private type D[A] = StateT[O, Pool, A]

  def gen[A](g: Gen[A]): D[A] = g match
    case Gen.Derived(ty)       => value(ty, 0).map(v => Fn.as[A](d.semantics.literal(v, ty)))
    case Gen.Const(a)          => StateT.pure(a)
    case Gen.OneOf(as)         => drawn(as.toList(below(as.size)))
    case Gen.Bind(first, next) => gen(first).flatMap(x => gen(next(x)))
    case Gen.Described(h, _)   => gen(h)

  /** A value of `ty` meeting every `always` of each type it holds, kept for the case's next values of `ty`. */
  def value(ty: Ty, depth: Int): D[Value] =
    meeting(ty)(chosen(ty, depth)).flatMap(v => StateT(pool => OptionT.some[Eval](pool.kept(ty, v) -> v)))

  /** From the generator given for the type (three times in four), an example's value, one drawn before, or fresh. */
  private def chosen(ty: Ty, depth: Int): D[Value] = StateT { pool =>
    val way = d.generatorFor(ty).filter(_ => chance(0.75)).map(givenBy(ty, _))
      .orElse(Option.when(d.seeds.of(ty).nonEmpty && chance(0.15))(pick(d.seeds.of(ty))))
      .orElse(Option.when(pool.of(ty).nonEmpty && chance(0.6))(pick(pool.of(ty))))
      .getOrElse(fresh(ty, depth))
    way.run(pool)
  }

  /** A given generator's value, as data, when it meets what always holds of every type it holds. */
  private def givenBy(ty: Ty, g: Gen[?]): D[Value] = gen(g).flatMapF { a =>
    val v = d.semantics.reflect(ScalaValue(a), ty)
    OptionT.fromOption[Eval](
      Option.when(d.rules.forall(_.broken(List(d.semantics.literal(v, ty)), List(ty), none).isEmpty))(v))
  }

  private def meeting(ty: Ty)(draw: D[Value]): D[Value] =
    val own = d.rules.filter(_.ty == ty)
    if own.isEmpty then draw
    else StateT(pool => OptionT(Eval.always(Iterator.continually(Drawing.run(draw, pool)).take(Derive.Tries)
      .flatten.find((_, v) => own.forall(_.holds(d.semantics.literal(v, ty), none))))))

  private def fresh(ty: Ty, depth: Int): D[Value] = ty match
    case Ty.Bool           => drawn(Value.Bool(chance(0.5)))
    case Ty.Num(_)         => drawn(Value.Num(number))
    case Ty.Str            => drawn(Value.Str(string))
    case Ty.Unit           => StateT.pure(Value.Unit)
    case Ty.ListOf(a)      => many(a, depth).map(Value.Many(_))
    case Ty.SetOf(a)       => many(a, depth).map(xs => Value.Many(xs.distinct))
    case Ty.MapOf(k, w)    => many(Ty.TupleOf(List(k, w)), depth).map(ps => Value.Pairs(ps.collect {
        case Value.Tuple(List(a, b)) => a -> b }.distinctBy(_._1)))
    case Ty.OptionOf(a)    =>
      either(StateT.pure(Value.Maybe(None)), value(a, depth + 1).map(x => Value.Maybe(Some(x))))
    case Ty.EitherOf(l, r) => either(value(l, depth + 1).map(Value.Inject(Side.Error, _)),
        value(r, depth + 1).map(Value.Inject(Side.Value, _)))
    case Ty.TupleOf(as)    => as.traverse(value(_, depth + 1)).map(Value.Tuple(_))
    case Ty.Data(n)        => d.vocabulary.dataType(n).fold(nothing)(data(_, depth))
    case _                 => nothing

  /** One of its constructors over drawn fields; deep down, a constructor without fields where there is one. */
  private def data(dt: DataType, depth: Int): D[Value] =
    val ctors = dt match
      case DataType.Product(_, _, fs) => List(CtorName("mk") -> fs.map(_.ty))
      case DataType.Sum(_, _, cs)     => cs.toList.map(c => c.name -> c.fields.map(_.ty))
    val small = ctors.filter(_._2.isEmpty)
    val from = if depth > 2 && small.nonEmpty then small else ctors
    drawn(from(below(from.size))).flatMap((c, fields) => fields.traverse(value(_, depth + 1)).map(Value.Data(c, _)))

  /** Fewer elements the deeper it is. */
  private def many(a: Ty, depth: Int): D[List[Value]] =
    drawn(below(size / (depth + 1) + 2)).flatMap(n => List.fill(n)(value(a, depth + 1)).sequence)

  /** The first, a quarter of the time; else the second. */
  private def either(first: => D[Value], second: => D[Value]): D[Value] =
    drawn(chance(0.25)).flatMap(f => if f then first else second)

  private def drawn[A](a: => A): D[A] = StateT(pool => OptionT(Eval.always(Some(pool -> a))))
  private def nothing: D[Value] = StateT.liftF(OptionT.none[Eval, Value])
  private def pick(xs: Vector[Value]): D[Value] = drawn(xs(below(xs.size)))
  private def below(n: Int): Int = if n <= 1 then 0 else random.nextInt(n)
  private def chance(p: Double): Boolean = random.nextDouble() < p
  private def none: Env = Env.of(Values.none)

  private def number: BigInt =
    if chance(0.3) then BigInt(below(3) - 1)
    else if d.seeds.numbers.nonEmpty && chance(0.4) then d.seeds.numbers(below(d.seeds.numbers.size)) + (below(3) - 1)
    else BigInt(below(20 * size + 1) - 10 * size)

  private def string: String = if chance(0.2) then "" else List.fill(below(4) + 1)("ab1"(below(3))).mkString

private[derive] object Drawing:
  /** A draw run from a pool: the pool after it and the value, or none. */
  def run[A](d: StateT[[x] =>> OptionT[Eval, x], Pool, A], pool: Pool): Option[(Pool, A)] = d.run(pool).value.value

package frflow
package types

import scala.deriving.Mirror
import scala.reflect.ClassTag

/** What a Scala type is in Lean, and how its values are taken apart: given for the standard types, derived for
  * case classes and enums (by their `Mirror`, at compile time). `of[T]` summons one.
  */
trait LeanType[A]:
  private[frflow] def shape: Shape
  /** The Lean type, and the declarations it needs (dependencies first). */
  def lean: String = Types.walk(this).lean
  def types: List[TypeDecl] = Types.walk(this).types

object LeanType:
  /** A case class, by its mirror (the standard types' instances below are more specific). */
  given product[T](using m: Mirror.ProductOf[T], ct: ClassTag[T], f: FieldsOf[m.MirroredElemTypes, m.MirroredElemLabels]): LeanType[T] =
    val name = qualified(ct.runtimeClass)
    data(Adt(name, ct.runtimeClass, isEnum = false, List(Ctor("mk", s"$name.mk", f.list, None, maker(m))), _ => 0))
  /** An enum, by its mirror. Recursive types are not supported (their derivation would not end). */
  given sum[T](using m: Mirror.SumOf[T], ct: ClassTag[T], cs: CasesOf[m.MirroredElemTypes, m.MirroredElemLabels]): LeanType[T] =
    val name = qualified(ct.runtimeClass)
    data(Adt(name, ct.runtimeClass, isEnum = true, cs.list(name), v => m.ordinal(v.asInstanceOf[T])))
  private[frflow] def maker(m: Mirror.Product): List[Any] => Any = xs => m.fromProduct(Tuple.fromArray(xs.toArray.map(_.asInstanceOf[Object])))

  private[frflow] def of[A](s: Shape): LeanType[A] = new LeanType[A] { private[frflow] val shape = s }
  private[frflow] def data[A](adt: Adt): LeanType[A] =
    val t = of[A](Shape.Data(adt))
    known.putIfAbsent(adt.cls, t)
    t
  /** Every case class and enum met so far, by class: what a boundary's operation, read by reflection, is typed with. */
  private val known = scala.collection.concurrent.TrieMap.empty[Class[?], LeanType[?]]

  /** The type of a boundary operation's parameter or result, read from its Java signature (`Term<CrmStore>`). */
  private[frflow] def ofJava(t: java.lang.reflect.Type): LeanType[?] = t match
    case p: java.lang.reflect.ParameterizedType =>
      val raw = p.getRawType.asInstanceOf[Class[?]]
      val as = p.getActualTypeArguments.toList.map(ofJava)
      raw.getName match
        case "frflow.term.Term" | "frflow.flow.Flow" => as.head
        case "scala.collection.immutable.List" => of(Shape.ListOf(as.head))
        case "scala.Option" => of(Shape.OptionOf(as.head))
        case "scala.util.Either" => of(Shape.EitherOf(as(0), as(1)))
        case "scala.collection.immutable.Map" => of(Shape.MapOf(as(0), as(1)))
        case "scala.collection.immutable.Set" => of(Shape.SetOf(as.head))
        case n if n.startsWith("scala.Tuple") => of(Shape.TupleOf(as))
        case n if n.startsWith("scala.Function") => of(Shape.FnOf(as.init, as.last))
        case _ => ofJava(raw)
    case c: Class[?] =>
      c.getName match
        case "java.lang.String" => summon[LeanType[String]]
        case "scala.math.BigInt" => summon[LeanType[BigInt]]
        case "boolean" | "java.lang.Boolean" => summon[LeanType[Boolean]]
        case "int" | "java.lang.Integer" => summon[LeanType[Int]]
        case "long" | "java.lang.Long" => summon[LeanType[Long]]
        case "void" | "scala.runtime.BoxedUnit" | "scala.Unit" => summon[LeanType[Unit]]
        case "frflow.boundary.World" => summon[LeanType[World]]
        case _ => Iterator.iterate[Class[?] | Null](c)(x => x.nn.getSuperclass).takeWhile(_ != null)
          .flatMap(x => known.get(x.nn)).nextOption().getOrElse(unknown)
    case _ => unknown
  private[frflow] def unknown[A]: LeanType[A] = of(Shape.Unknown)

  given LeanType[Boolean] = of(Shape.Prop)
  given LeanType[Int] = of(Shape.Num(NumKind.IntN))
  given LeanType[Long] = of(Shape.Num(NumKind.LongN))
  given LeanType[BigInt] = of(Shape.Num(NumKind.BigN))
  given LeanType[String] = of(Shape.Str)
  given LeanType[Unit] = of(Shape.UnitT)
  given [A](using a: LeanType[A]): LeanType[List[A]] = of(Shape.ListOf(a))
  given [A](using a: LeanType[A]): LeanType[::[A]] = of(Shape.ListOf(a))
  given LeanType[Nil.type] = of(Shape.ListOf(unknown))
  given [A](using a: LeanType[A]): LeanType[Option[A]] = of(Shape.OptionOf(a))
  given [A](using a: LeanType[A]): LeanType[Some[A]] = of(Shape.OptionOf(a))
  given LeanType[None.type] = of(Shape.OptionOf(unknown))
  given [E, A](using e: LeanType[E], a: LeanType[A]): LeanType[Either[E, A]] = of(Shape.EitherOf(e, a))
  given [K, V](using k: LeanType[K], v: LeanType[V]): LeanType[Map[K, V]] = of(Shape.MapOf(k, v))
  given [A](using a: LeanType[A]): LeanType[Set[A]] = of(Shape.SetOf(a))
  given [A, B](using a: LeanType[A], b: LeanType[B]): LeanType[(A, B)] = of(Shape.TupleOf(List(a, b)))
  given [A, B, C](using a: LeanType[A], b: LeanType[B], c: LeanType[C]): LeanType[(A, B, C)] = of(Shape.TupleOf(List(a, b, c)))
  given [R](using r: LeanType[R]): LeanType[() => R] = of(Shape.FnOf(Nil, r))
  given [A, R](using a: LeanType[A], r: LeanType[R]): LeanType[A => R] = of(Shape.FnOf(List(a), r))
  given [A, B, R](using a: LeanType[A], b: LeanType[B], r: LeanType[R]): LeanType[(A, B) => R] = of(Shape.FnOf(List(a, b), r))
  given [A, B, C, R](using a: LeanType[A], b: LeanType[B], c: LeanType[C], r: LeanType[R]): LeanType[(A, B, C) => R] =
    of(Shape.FnOf(List(a, b, c), r))
  given [A, B, C, D, R](using a: LeanType[A], b: LeanType[B], c: LeanType[C], d: LeanType[D], r: LeanType[R]): LeanType[(A, B, C, D) => R] =
    of(Shape.FnOf(List(a, b, c, d), r))
  given [A, B, C, D, E, R](using a: LeanType[A], b: LeanType[B], c: LeanType[C], d: LeanType[D], e: LeanType[E], r: LeanType[R]): LeanType[(A, B, C, D, E) => R] =
    of(Shape.FnOf(List(a, b, c, d, e), r))
  given [A, B, C, D, E, F, R](using a: LeanType[A], b: LeanType[B], c: LeanType[C], d: LeanType[D], e: LeanType[E], f: LeanType[F],
      r: LeanType[R]): LeanType[(A, B, C, D, E, F) => R] =
    of(Shape.FnOf(List(a, b, c, d, e, f), r))
  given [R](using r: LeanType[R]): LeanType[Flow[R]] = of(Shape.FlowOf(r))

  /** The owner chain without packages, as Lean names it: `Model.Session`, `Search.ById`. */
  private[frflow] def qualified(c: Class[?]): String =
    val pkg = c.getPackageName
    val rest = if pkg.isEmpty then c.getName else c.getName.stripPrefix(pkg + ".")
    rest.replaceAll("[^$]*\\$package\\$", "").split('$').filter(_.nonEmpty).map(Names.ident).mkString(".")

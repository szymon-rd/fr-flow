package frflow


import scala.deriving.Mirror
import scala.reflect.ClassTag

/** What a Scala type is in Lean, and how its values are taken apart: given for the standard types, derived for
  * case classes and enums (by their `Mirror`, at compile time; nothing reads their code). `of[T]` summons one.
  */
trait LeanType[A]:
  private[frflow] def shape: Shape
  /** The Lean type, and the declarations it needs (dependencies first). */
  def lean: String = Types.walk(this).lean
  def types: List[TypeDecl] = Types.walk(this).types

private[frflow] enum Shape:
  case Prop, Str, UnitT, Unknown
  /** `bounded`: a Scala Int or Long, which wraps around where Lean's Int does not. */
  case Num(bounded: Boolean)
  case ListOf(a: LeanType[?])
  case OptionOf(a: LeanType[?])
  case MapOf(k: LeanType[?], v: LeanType[?])
  case SetOf(a: LeanType[?])
  case TupleOf(as: List[LeanType[?]])
  case FnOf(as: List[LeanType[?]], r: LeanType[?])
  case Opq(o: Opaque)
  case Data(adt: Adt)
  /** The states of the boundaries' models (Lean's `World`). */
  case WorldT
  /** A flow's result, as an operation's: run from a world, the result and the world after. */
  case FlowOf(r: LeanType[?])

/** A case class (one constructor, `mk`) or an enum (its cases, in order). */
private[frflow] final class Adt(val name: String, val cls: Class[?], val isEnum: Boolean, ctorList: => List[Ctor],
    val ordinal: Any => Int):
  lazy val ctors: List[Ctor] = ctorList
  def scalaName: String = cls.getSimpleName
  def ctorOf(v: Any): Ctor = ctors(ordinal(v))
  /** Lean equality is structural: a supertype that redefines `equals` would mean something else at run time. */
  def redefinedEquality: Option[String] =
    val standard = Set("java.lang.Object", "scala.Product", "scala.Equals", "java.io.Serializable", "scala.reflect.Enum",
      "scala.runtime.EnumValue", "scala.deriving.Mirror", "scala.deriving.Mirror$Product", "scala.deriving.Mirror$Singleton")
    def supers(c: Class[?]): List[Class[?]] =
      (Option(c.getSuperclass).toList ++ c.getInterfaces.toList).flatMap(s => s :: supers(s))
    supers(cls).distinct.filterNot(c => standard(c.getName)).flatMap { s =>
      s.getDeclaredMethods.filter(m => (m.getName == "equals" && m.getParameterCount == 1) || (m.getName == "hashCode" && m.getParameterCount == 0))
        .filterNot(_.isSynthetic).map(m => s"$scalaName redefines ${m.getName} (in ${s.getSimpleName})")
    }.headOption.orElse(ownEquality)

  /** Its own equality, unless as Scala generates it: `equals` reads every field, `hashCode` hashes the product or
    * every field, `canEqual` only tests the type (an enum's own class declares none of them). Read from the class
    * files: a program's `equals` that reads every field does what the generated one does.
    */
  private def ownEquality: Option[String] =
    val Eq = ("equals", "(Ljava/lang/Object;)Z")
    val Hash = ("hashCode", "()I")
    val CanEq = ("canEqual", "(Ljava/lang/Object;)Z")
    val classes: List[(Class[?], List[String], Boolean)] =
      if isEnum then (cls, Nil, true) :: ctors.filter(_.singleton.isEmpty).flatMap { c =>
        scala.util.Try(Class.forName(s"${cls.getName}$$${c.label}", false, cls.getClassLoader)).toOption.map(k => (k, c.fields.map(_._1), false))
      }
      else List((cls, ctors.head.fields.map(_._1), false))
    classes.flatMap { (c, fields, base) =>
      Bytecode.of(c).toList.flatMap { bc =>
        def has(m: (String, String)) = bc.code(m._1, m._2).isDefined
        def calls(m: (String, String)) = bc.calls(m._1, m._2)
        val hashesAll = calls(Hash).exists(Set("productHash", "caseClassHash")) || fields.forall(calls(Hash))
        List(
          Option.when(has(Eq) && (base || !fields.forall(calls(Eq))))("equals"),
          Option.when(has(Hash) && (base || !hashesAll))("hashCode"),
          Option.when(has(CanEq) && (base || calls(CanEq).nonEmpty))("canEqual")
        ).flatten.map(m => s"${c.getSimpleName} redefines $m (in ${c.getSimpleName})")
      }
    }.headOption
  def ctor(label: String): Ctor = ctors.find(_.label == label).getOrElse(throw IllegalArgumentException(s"$name has no case $label"))

/** `label` as Scala names it; `lean`, the constructor's Lean name; a singleton's value; making one from its fields. */
private[frflow] final class Ctor(val label: String, val lean: String, val fields: List[(String, LeanType[?])],
    val singleton: Option[Any], val make: List[Any] => Any)

/** The fields of a case class (or of an enum's case): their names and types, found as any given is. */
trait FieldsOf[Ts <: Tuple, Ls <: Tuple]:
  private[frflow] def list: List[(String, LeanType[?])]
object FieldsOf:
  given FieldsOf[EmptyTuple, EmptyTuple] with
    private[frflow] def list = Nil
  given [H, T <: Tuple, L <: String, Ls <: Tuple](using h: LeanType[H], l: ValueOf[L], t: FieldsOf[T, Ls]): FieldsOf[H *: T, L *: Ls] with
    private[frflow] def list = (l.value -> h) :: t.list

/** The cases of an enum, in order. */
trait CasesOf[Cs <: Tuple, Ls <: Tuple]:
  private[frflow] def list(owner: String): List[Ctor]
object CasesOf:
  given CasesOf[EmptyTuple, EmptyTuple] with
    private[frflow] def list(owner: String) = Nil
  given [C, Cs <: Tuple, L <: String, Ls <: Tuple](using m: Mirror.ProductOf[C], f: FieldsOf[m.MirroredElemTypes, m.MirroredElemLabels],
      l: ValueOf[L], rest: CasesOf[Cs, Ls]): CasesOf[C *: Cs, L *: Ls] with
    private[frflow] def list(owner: String) =
      val fs = f.list
      // A case without fields is a value of the enum (`Search.Everything`).
      Ctor(l.value, s"$owner.${Names.ident(l.value)}", fs, Option.when(fs.isEmpty)(m.fromProduct(EmptyTuple)), LeanType.maker(m)) ::
        rest.list(owner)

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
        case "frflow.Term" | "frflow.Flow" => as.head
        case "scala.collection.immutable.List" => of(Shape.ListOf(as.head))
        case "scala.Option" => of(Shape.OptionOf(as.head))
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
        case "frflow.World" => summon[LeanType[World]]
        case _ => Iterator.iterate[Class[?] | Null](c)(x => x.nn.getSuperclass).takeWhile(_ != null)
          .flatMap(x => known.get(x.nn)).nextOption().getOrElse(unknown)
    case _ => unknown
  private[frflow] def unknown[A]: LeanType[A] = of(Shape.Unknown)

  given LeanType[Boolean] = of(Shape.Prop)
  given LeanType[Int] = of(Shape.Num(bounded = true))
  given LeanType[Long] = of(Shape.Num(bounded = true))
  given LeanType[BigInt] = of(Shape.Num(bounded = false))
  given LeanType[String] = of(Shape.Str)
  given LeanType[Unit] = of(Shape.UnitT)
  given [A](using a: LeanType[A]): LeanType[List[A]] = of(Shape.ListOf(a))
  given [A](using a: LeanType[A]): LeanType[::[A]] = of(Shape.ListOf(a))
  given LeanType[Nil.type] = of(Shape.ListOf(unknown))
  given [A](using a: LeanType[A]): LeanType[Option[A]] = of(Shape.OptionOf(a))
  given [A](using a: LeanType[A]): LeanType[Some[A]] = of(Shape.OptionOf(a))
  given LeanType[None.type] = of(Shape.OptionOf(unknown))
  given [K, V](using k: LeanType[K], v: LeanType[V]): LeanType[Map[K, V]] = of(Shape.MapOf(k, v))
  given [A](using a: LeanType[A]): LeanType[Set[A]] = of(Shape.SetOf(a))
  given [A, B](using a: LeanType[A], b: LeanType[B]): LeanType[(A, B)] = of(Shape.TupleOf(List(a, b)))
  given [A, B, C](using a: LeanType[A], b: LeanType[B], c: LeanType[C]): LeanType[(A, B, C)] = of(Shape.TupleOf(List(a, b, c)))
  given [A, R](using a: LeanType[A], r: LeanType[R]): LeanType[A => R] = of(Shape.FnOf(List(a), r))
  given [A, B, R](using a: LeanType[A], b: LeanType[B], r: LeanType[R]): LeanType[(A, B) => R] = of(Shape.FnOf(List(a, b), r))
  given [A, B, C, R](using a: LeanType[A], b: LeanType[B], c: LeanType[C], r: LeanType[R]): LeanType[(A, B, C) => R] =
    of(Shape.FnOf(List(a, b, c), r))
  given [A, B, C, D, R](using a: LeanType[A], b: LeanType[B], c: LeanType[C], d: LeanType[D], r: LeanType[R]): LeanType[(A, B, C, D) => R] =
    of(Shape.FnOf(List(a, b, c, d), r))
  given [A, B, C, D, E, R](using a: LeanType[A], b: LeanType[B], c: LeanType[C], d: LeanType[D], e: LeanType[E], r: LeanType[R]): LeanType[(A, B, C, D, E) => R] =
    of(Shape.FnOf(List(a, b, c, d, e), r))
  given [R](using r: LeanType[R]): LeanType[Flow[R]] = of(Shape.FlowOf(r))

  /** The owner chain without packages, as Lean names it: `Model.Session`, `Search.ById`. */
  private[frflow] def qualified(c: Class[?]): String =
    val pkg = c.getPackageName
    val rest = if pkg.isEmpty then c.getName else c.getName.stripPrefix(pkg + ".")
    rest.replaceAll("[^$]*\\$package\\$", "").split('$').filter(_.nonEmpty).map(Names.ident).mkString(".")


/** A Lean type's text and the declarations it needs, in the order Lean must read them. */
private[frflow] final case class Walked(lean: String, types: List[TypeDecl], opaques: List[Opaque])

/** Walking a type: what the Lean printer does for each type it meets (it declares what it needs, nested types first). */
private[frflow] final class Types:
  val decls = scala.collection.mutable.LinkedHashMap.empty[String, TypeDecl]
  private val inProgress = scala.collection.mutable.Set.empty[String]
  val opaques = scala.collection.mutable.LinkedHashMap.empty[String, Opaque]

  def tpe(t: LeanType[?]): String = t.shape match
    case Shape.Prop          => "Prop"
    case Shape.Num(_)        => "Int"
    case Shape.Str           => "String"
    case Shape.UnitT         => "Unit"
    case Shape.Unknown       => throw IllegalArgumentException("FrFlow: cannot infer the type here; give it (as in `none[UserId]`)")
    case Shape.MapOf(k, v)   => val kt = tpe(k); s"($kt → Option ${tpe(v)})"
    case Shape.SetOf(a)      => s"(${tpe(a)} → Prop)"
    case Shape.ListOf(a)     => s"(List ${tpe(a)})"
    case Shape.OptionOf(a)   => s"(Option ${tpe(a)})"
    case Shape.TupleOf(as)   => as.map(tpe).mkString("(", " × ", ")")
    case Shape.FnOf(as, r)   => "(" + (as :+ r).map(tpe).mkString(" → ") + ")"
    case Shape.Opq(o)        => val n = Names.ident(o.name); opaques.getOrElseUpdate(n, o); n
    case Shape.Data(adt)     => declare(adt)
    case Shape.WorldT        => "World"
    case Shape.FlowOf(r)     => s"(World → (${tpe(r)} × World))"

  def declare(adt: Adt): String =
    if !decls.contains(adt.name) && !inProgress(adt.name) then
      adt.redefinedEquality.foreach(e => throw IllegalArgumentException(s"FrFlow: $e: domain types must keep structural equality"))
      inProgress += adt.name
      val leanCtors = adt.ctors.map { c =>
        c.fields.foreach((f, t) => if t.shape.isInstanceOf[Shape.FnOf] then
          throw IllegalArgumentException(s"FrFlow: ${adt.scalaName}.$f is a function: a domain type's fields must be data"))
        (if adt.isEnum then Names.ident(c.label) else "mk") -> c.fields.map((f, t) => Names.ident(f) -> tpe(t))
      }
      val lean =
        if adt.isEnum then s"inductive ${adt.name} where\n" + leanCtors.map((c, fs) => s"  | $c${fs.map((n, t) => s" ($n : $t)").mkString}").mkString("\n")
        else
          val fs = leanCtors.head._2
          s"structure ${adt.name}" + (if fs.isEmpty then "" else " where\n" + fs.map((n, t) => s"  $n : $t").mkString("\n"))
      def shape(fs: List[(String, LeanType[?])]) = if fs.isEmpty then "" else fs.map((n, t) => s"$n: ${Types.scala(t)}").mkString("(", ", ", ")")
      val scala =
        if adt.isEnum then s"enum ${adt.scalaName}: " + adt.ctors.map(c => "case " + c.label + shape(c.fields)).mkString(", ")
        else s"case class ${adt.scalaName}${shape(adt.ctors.head.fields)}"
      val uses = adt.ctors.flatMap(_.fields.map(_._2)).flatMap(Types.adts).map(_.name).distinct.filterNot(_ == adt.name)
      decls(adt.name) = TypeDecl(adt.name, lean, uses, scala, leanCtors)
      inProgress -= adt.name
    adt.name

private[frflow] object Types:
  def walk(t: LeanType[?]): Walked =
    val w = Types()
    val lean = w.tpe(t)
    Walked(lean, w.decls.values.toList, w.opaques.values.toList)

  /** The case classes and enums a type names, itself or in its arguments. */
  def adts(t: LeanType[?]): List[Adt] = t.shape match
    case Shape.Data(a)                     => List(a)
    case Shape.ListOf(a)                   => adts(a)
    case Shape.OptionOf(a)                 => adts(a)
    case Shape.SetOf(a)                    => adts(a)
    case Shape.MapOf(k, v)                 => adts(k) ++ adts(v)
    case Shape.TupleOf(as)                 => as.flatMap(adts)
    case Shape.FnOf(as, r)                 => (as :+ r).flatMap(adts)
    case Shape.FlowOf(r)                   => adts(r)
    case _                                 => Nil

  /** The Scala type as written: what a decision on a node using it binds. */
  def scala(t: LeanType[?]): String = t.shape match
    case Shape.Prop          => "Boolean"
    case Shape.Num(b)        => if b then "Int" else "BigInt"
    case Shape.Str           => "String"
    case Shape.UnitT         => "Unit"
    case Shape.Unknown       => "?"
    case Shape.ListOf(a)     => s"List[${scala(a)}]"
    case Shape.OptionOf(a)   => s"Option[${scala(a)}]"
    case Shape.MapOf(k, v)   => s"Map[${scala(k)}, ${scala(v)}]"
    case Shape.SetOf(a)      => s"Set[${scala(a)}]"
    case Shape.TupleOf(as)   => as.map(scala).mkString("(", ", ", ")")
    case Shape.FnOf(as, r)   => (if as.size == 1 then scala(as.head) else as.map(scala).mkString("(", ", ", ")")) + " => " + scala(r)
    case Shape.Opq(o)        => s"${o.name}.T"
    case Shape.Data(a)       => a.scalaName
    case Shape.WorldT        => "World"
    case Shape.FlowOf(r)     => s"Flow[${scala(r)}]"

  /** Whether the type names the boundaries' world (Lean's `World`, declared with the boundaries). */
  def mentionsWorld(t: LeanType[?]): Boolean = t.shape match
    case Shape.WorldT | Shape.FlowOf(_) => true
    case Shape.ListOf(a)   => mentionsWorld(a)
    case Shape.OptionOf(a) => mentionsWorld(a)
    case Shape.SetOf(a)    => mentionsWorld(a)
    case Shape.MapOf(k, v) => mentionsWorld(k) || mentionsWorld(v)
    case Shape.TupleOf(as) => as.exists(mentionsWorld)
    case Shape.FnOf(as, r) => (as :+ r).exists(mentionsWorld)
    case _                 => false

  /** Whether a value of the type holds an Int or a Long, however deep. */
  def bounded(t: LeanType[?], seen: Set[String] = Set.empty): Boolean = t.shape match
    case Shape.Num(b)      => b
    case Shape.Data(a)     => !seen(a.name) && a.ctors.exists(_.fields.exists((_, f) => bounded(f, seen + a.name)))
    case Shape.ListOf(a)   => bounded(a, seen)
    case Shape.OptionOf(a) => bounded(a, seen)
    case Shape.SetOf(a)    => bounded(a, seen)
    case Shape.MapOf(k, v) => bounded(k, seen) || bounded(v, seen)
    case Shape.TupleOf(as) => as.exists(bounded(_, seen))
    case Shape.FnOf(as, r) => (as :+ r).exists(bounded(_, seen))
    case _                 => false

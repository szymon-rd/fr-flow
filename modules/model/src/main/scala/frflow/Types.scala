package frflow

import frflow.types.Adt
import frflow.types.Shape

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
    case Shape.EitherOf(e, a) => val te = tpe(e); s"(Except $te ${tpe(a)})"
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
    case Shape.EitherOf(e, a)              => adts(e) ++ adts(a)
    case Shape.SetOf(a)                    => adts(a)
    case Shape.MapOf(k, v)                 => adts(k) ++ adts(v)
    case Shape.TupleOf(as)                 => as.flatMap(adts)
    case Shape.FnOf(as, r)                 => (as :+ r).flatMap(adts)
    case Shape.FlowOf(r)                   => adts(r)
    case _                                 => Nil

  /** The Scala type as written: what a decision on a node using it binds. */
  def scala(t: LeanType[?]): String = t.shape match
    case Shape.Prop          => "Boolean"
    case Shape.Num(k)        => if k.bounded then "Int" else "BigInt"
    case Shape.Str           => "String"
    case Shape.UnitT         => "Unit"
    case Shape.Unknown       => "?"
    case Shape.ListOf(a)     => s"List[${scala(a)}]"
    case Shape.OptionOf(a)   => s"Option[${scala(a)}]"
    case Shape.EitherOf(e, a) => s"Either[${scala(e)}, ${scala(a)}]"
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
    case Shape.EitherOf(e, a) => mentionsWorld(e) || mentionsWorld(a)
    case Shape.SetOf(a)    => mentionsWorld(a)
    case Shape.MapOf(k, v) => mentionsWorld(k) || mentionsWorld(v)
    case Shape.TupleOf(as) => as.exists(mentionsWorld)
    case Shape.FnOf(as, r) => (as :+ r).exists(mentionsWorld)
    case _                 => false

  /** Whether a value of the type holds an Int or a Long, however deep. */
  def bounded(t: LeanType[?], seen: Set[String] = Set.empty): Boolean = t.shape match
    case Shape.Num(k)      => k.bounded
    case Shape.Data(a)     => !seen(a.name) && a.ctors.exists(_.fields.exists((_, f) => bounded(f, seen + a.name)))
    case Shape.ListOf(a)   => bounded(a, seen)
    case Shape.OptionOf(a) => bounded(a, seen)
    case Shape.EitherOf(e, a) => bounded(e, seen) || bounded(a, seen)
    case Shape.SetOf(a)    => bounded(a, seen)
    case Shape.MapOf(k, v) => bounded(k, seen) || bounded(v, seen)
    case Shape.TupleOf(as) => as.exists(bounded(_, seen))
    case Shape.FnOf(as, r) => (as :+ r).exists(bounded(_, seen))
    case _                 => false

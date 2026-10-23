package frflow
package lean

import cats.syntax.all.*

/** Scala values as Lean terms of a knowledge base's domain. */
final class LeanValues(kb: KnowledgeBase):
  private val K = kb.name
  private val typeNames: Set[String] = kb.types.map(_.name).toSet

  /** The Lean name of a domain class, as `Lift` declares it (the owner chain without packages). */
  private def leanName(c: Class[?]): String =
    val pkg = c.getPackageName
    val rest = if pkg.isEmpty then c.getName else c.getName.stripPrefix(pkg + ".")
    rest.replaceAll("[^$]*\\$package\\$", "").split('$').filter(_.nonEmpty).map(Names.ident).mkString(".")

  private def int(b: BigInt) = if b < 0 then s"($b)" else b.toString
  private def ctor(name: String, args: List[String]) = if args.isEmpty then s"$K.$name" else s"($K.$name ${args.mkString(" ")})"
  private def all(xs: Iterator[Any]): Option[List[String]] = xs.map(leanValue).toList.sequence

  /** A lookup, as Lean has it for a map: `if k' = k₁ then some v₁ else … none`. */
  def lookup(pairs: List[(String, String)]): String =
    pairs.foldRight("none")((kv, rest) => s"if k' = ${kv._1} then some ${kv._2} else $rest")

  /** A Scala value as a Lean term of the domain: None for what Lean has no value for (a function, an
    * opaque value, a Map of what Lean has no value for).
    */
  def leanValue(v: Any): Option[String] = v match
    case b: Boolean => Some(if b then "True" else "False")
    case i: Int     => Some(int(BigInt(i)))
    case l: Long    => Some(int(BigInt(l)))
    case b: BigInt  => Some(int(b))
    case s: String  => Some(Names.string(s))
    case ()         => Some("()")
    case None       => Some("none")
    case Some(x)    => leanValue(x).map(t => s"(some $t)")
    case l: List[?] => all(l.iterator).map(_.mkString("[", ", ", "]"))
    // A map, as the function Lean has for it (see `Lift.tpe`); a set, as its membership.
    case m: Map[?, ?] => m.toList.traverse((k, v) => (leanValue(k), leanValue(v)).tupled).map(kvs => s"(fun k' => ${lookup(kvs)})")
    case st: Set[?] => all(st.iterator).map(xs => s"(fun y' => ${(xs.map(x => s"y' = $x") :+ "False").mkString(" ∨ ")})")
    case t: Product if t.getClass.getName.startsWith("scala.Tuple") => all(t.productIterator).map(_.mkString("(", ", ", ")"))
    case e: scala.reflect.Enum =>
      val c = if typeNames(leanName(e.getClass)) then e.getClass else e.getClass.getSuperclass
      Option.when(typeNames(leanName(c)))(leanName(c)).flatMap(t => all(e.productIterator).map(ctor(s"$t.${Names.ident(e.productPrefix)}", _)))
    case p: Product if typeNames(leanName(p.getClass)) => all(p.productIterator).map(ctor(s"${leanName(p.getClass)}.mk", _))
    case _ => None

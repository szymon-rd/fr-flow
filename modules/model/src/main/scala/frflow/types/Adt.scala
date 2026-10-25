package frflow
package types

import frflow.program.Bytecode
import scala.deriving.Mirror

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

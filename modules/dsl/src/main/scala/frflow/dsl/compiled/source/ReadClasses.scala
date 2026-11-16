package frflow.dsl.compiled.source

import frflow.core.code.ClassFacts
import frflow.core.threads.Datum
import java.lang.reflect.Modifier
import scala.util.Try

/** What is known of the classes a tree mentions, from their class files: a tree names a class where it types a
  * value, and in the signature of a method it calls. A class that is not found is one nothing is known of.
  */
object ReadClasses:
  def of(tree: Datum, loader: ClassLoader): ClassFacts =
    val found = named(tree).distinct.flatMap(n => load(n, loader).map(n -> _))
    ClassFacts(found.collect { case (n, c) if identity(c) => n }.sorted,
      found.collect { case (n, c) if classOf[Throwable].isAssignableFrom(c) => n }.sorted,
      found.flatMap((n, c) => function(c).map(m => s"$n $m ")).sorted,
      (found.collect { case (n, c) if heir(c) => n } ++ functions(tree, loader)).distinct.sorted)

  /** The classes the tree defines that are functions of Scala's: an object of one can be given where a function
    * is taken. A class made inside a method is not found by its name, and is not among them.
    */
  private def functions(tree: Datum, loader: ClassLoader): List[String] =
    defined(tree).distinct.filter(n => load(n, loader).exists(c => above(c).exists(_.getName.matches(function))))

  private val function = "scala\\.Function\\d+"

  private def defined(d: Datum): List[String] = d match
    case Datum.Of("ClassDef", Datum.Text(key) :: rest) => key :: rest.flatMap(defined)
    case Datum.Of(_, args)                             => args.flatMap(defined)
    case Datum.Many(elems)                             => elems.flatMap(defined)
    case Datum.Maybe(value)                            => value.toList.flatMap(defined)
    case _                                             => Nil

  /** Every class and interface a class is below. */
  private def above(c: Class[?]): List[Class[?]] =
    val direct = Option(c.getSuperclass).toList ++ c.getInterfaces.toList
    direct ++ direct.flatMap(above)

  /** The names a tree holds that could be a class's: a text, or a part of a signature. */
  private def named(d: Datum): List[String] = d match
    case Datum.Of(_, args)  => args.flatMap(named)
    case Datum.Many(elems)  => elems.flatMap(named)
    case Datum.Maybe(value) => value.toList.flatMap(named)
    case Datum.Text(value)  => value.split("[,: ]").toList.filter(_.matches(className))
    case _                  => Nil

  private val className = "[A-Za-z_][A-Za-z0-9_.$]*\\.[A-Za-z0-9_.$]+"

  /** The class a tree names: a class inside another is `Outer$.Inner` in a tree, `Outer$Inner` on the JVM. */
  private def load(name: String, loader: ClassLoader): Option[Class[?]] =
    Try(Class.forName(name.replace("$.", "$"), false, loader)).toOption

  /** An object of the class is known by its identity: a class of the JDK that can be made and keeps `Object`'s
    * `equals`, and is neither what is thrown nor `Object` or `Class` themselves. A class outside the JDK that
    * extends it and says what `equals` is is not considered.
    */
  private def identity(c: Class[?]): Boolean =
    !c.isInterface && !c.isArray && !c.isPrimitive && !Modifier.isAbstract(c.getModifiers) &&
      c.getName.startsWith("java.") &&
      c != classOf[Object] && c != classOf[Class[?]] && !classOf[Throwable].isAssignableFrom(c) &&
      Try(c.getMethod("equals", classOf[Object]).getDeclaringClass == classOf[Object]).getOrElse(false)

  /** A class outside the JDK that is below a class known by its identity. */
  private def heir(c: Class[?]): Boolean =
    !c.getName.startsWith("java.") &&
      Iterator.iterate(c.getSuperclass)(_.getSuperclass).takeWhile(_ != null).exists(identity)

  /** The one method of an interface a function can be taken as, if it has one. */
  private def function(c: Class[?]): Option[String] =
    val own = Try(c.getMethods.toList).getOrElse(Nil).filter(m => Modifier.isAbstract(m.getModifiers) &&
      !Set("equals", "hashCode", "toString")(m.getName)).map(_.getName).distinct
    Option.when(c.isInterface && own.sizeIs == 1)(own.head)

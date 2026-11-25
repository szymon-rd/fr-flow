package frflow.dsl.compiled.normal

import frflow.core.normal.NormalProgram
import frflow.dsl.compiled.Inspect
import frflow.dsl.lifted.NotRead
import scala.quoted.Quotes

/** Stage 1 of the translation (`docs/EFFECT-TREES.md`, 4.1): compiled Scala read into normalised Scala. The
  * classes of the TASTy files a class was compiled beside, each method as statements in the order Scala
  * evaluates them. Nothing is interpreted. Scala that is not read is refused with its place (`NotRead`).
  */
object Normalise:
  /** The program of the files, of the directory `cls` was compiled into, whose paths `keep` takes. */
  def apply(cls: Class[?], keep: String => Boolean): NormalProgram =
    Inspect.files(cls, keep)(q => files => Reader[q.type](q).program(files.sortBy(_._1)))

  /** Of the files `keep` takes: each method they hold, by its class and name, with why it is not read, if it
    * is not. A measure of how much of some code is read; nothing is refused.
    */
  def survey(cls: Class[?], keep: String => Boolean): List[(String, Option[String])] =
    Inspect.files(cls, _ => true)(q => files =>
      Reader[q.type](q).surveyed(files.filter((path, _) => keep(path)).sortBy(_._1).map(_._2)))

  private final class Reader[Q <: Quotes & Singleton](val q: Q) extends ReadClasses:
    import q.reflect.*

    def surveyed(trees: List[Tree]): List[(String, Option[String])] =
      val all = trees.flatMap(everyClass)
      val named = all.map(c => c -> refusal(name(c)))
      named.flatMap((c, unnamed) => c.body.collect { case d: DefDef if d.rhs.isDefined =>
        s"${c.name}.${d.name}" -> unnamed.orElse(refusal(tried(d))) })

    private def everyClass(t: Tree): List[ClassDef] =
      val found = new TreeAccumulator[List[ClassDef]]:
        def foldTree(seen: List[ClassDef], t: Tree)(owner: Symbol): List[ClassDef] = t match
          case c: ClassDef => foldOverTree(seen :+ c, t)(owner)
          case _           => foldOverTree(seen, t)(owner)
      found.foldTree(Nil, t)(Symbol.spliceOwner)

    /** Why `read` is refused, without its place; nothing if it is read. */
    private def refusal(read: => Any): Option[String] =
      try { val _ = read; None }
      catch case e: NotRead => Some(e.getMessage.stripPrefix("FrFlow: ").split(" is not read into").head)

    def program(files: List[(String, q.reflect.Tree)]): NormalProgram =
      val all = files.flatMap((_, tree) => declared(tree))
      all.foreach(name)
      val read = all.flatMap(routines)
      NormalProgram(all.map(_.symbol.fullName), classes.values.toList, fields.values.toList, read,
        outside.values.toList)

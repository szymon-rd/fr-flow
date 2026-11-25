package frflow.dsl.compiled.normal

import frflow.core.normal.NormalProgram
import frflow.dsl.compiled.Inspect
import scala.quoted.Quotes

/** Stage 1 of the translation (`docs/EFFECT-TREES.md`, 4.1): compiled Scala read into normalised Scala. The
  * classes of the TASTy files a class was compiled beside, each method as statements in the order Scala
  * evaluates them. Nothing is interpreted. Scala that is not read is refused with its place (`NotRead`).
  */
object Normalise:
  /** The program of the files, of the directory `cls` was compiled into, whose paths `keep` takes. */
  def apply(cls: Class[?], keep: String => Boolean): NormalProgram =
    Inspect.files(cls, keep)(q => files => Reader[q.type](q).program(files.sortBy(_._1)))

  private final class Reader[Q <: Quotes & Singleton](val q: Q) extends ReadClasses:
    def program(files: List[(String, q.reflect.Tree)]): NormalProgram =
      val all = files.flatMap((_, tree) => declared(tree))
      all.foreach(name)
      val read = all.flatMap(routines)
      NormalProgram(all.map(_.symbol.fullName), classes.values.toList, fields.values.toList, read,
        outside.values.toList)

package frflow.dsl.compiled.effect

import frflow.core.effect.Program
import frflow.dsl.compiled.Inspect
import frflow.dsl.lifted.NotRead
import scala.quoted.Quotes

/** Compiled Scala read as trees of effects (`docs/EFFECT-TREES.md`): the classes of the TASTy files a class was
  * compiled beside, each method the tree of what it does. What is evaluated without effect is a term in the
  * tree; a variable of a method is the value it has; a loop's state is the variables it assigns. Scala the
  * emitter does not read yet is refused with its place (`NotRead`), never passed over.
  */
object EmitEffects:
  /** The program of the files, of the directory `cls` was compiled into, whose paths `keep` takes. */
  def apply(cls: Class[?], keep: String => Boolean): Program =
    Inspect.files(cls, keep)(q => files => Emitter[q.type](q).program(files.sortBy(_._1)))

  private final class Emitter[Q <: Quotes & Singleton](val q: Q) extends EmitClasses:
    def program(files: List[(String, q.reflect.Tree)]): Program =
      val all = files.flatMap((_, tree) => declared(tree))
      all.foreach(name)
      val trees_ = all.flatMap(trees)
      val read = Program(all.map(_.symbol.fullName), classes.values.toList, fields.values.toList, trees_,
        outside.values.toList)
      read.clashes.headOption.foreach(name => NotRead.raise(using q)(
        s"FrFlow: two things of the code would be written `$name`, so it is not read into trees of effects", None))
      read

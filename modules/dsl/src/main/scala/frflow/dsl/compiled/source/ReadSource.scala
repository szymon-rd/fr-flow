package frflow.dsl.compiled.source

import frflow.core.threads.Datum
import frflow.dsl.compiled.Inspect
import scala.quoted.Quotes

/** Compiled Scala read as the trees its TASTy holds, whole: each TASTy file of the place a class was compiled
  * into (a directory, a jar), as the data `modules/proof/rocq/FrFlow/Scala/Tree.v` declares. Nothing is chosen
  * in the reading: every form of tree and of type has its constructor, a form with none is refused, and so the
  * data is the code. What the code means is said in Rocq, of this data.
  */
object ReadSource:
  /** Every TASTy file where `cls` was compiled into: its path, and the tree it holds. */
  def apply(cls: Class[?]): List[(String, Datum)] =
    Inspect.files(cls)(q => files => files.sortBy(_._1).map((path, ast) => path -> Reader[q.type](q).tree(ast)))

  private final class Reader[Q <: Quotes & Singleton](val q: Q) extends SourceDefs

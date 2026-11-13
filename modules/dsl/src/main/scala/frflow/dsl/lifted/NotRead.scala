package frflow.dsl.lifted

import scala.quoted.*
import scala.util.Try

/** Scala FrFlow does not read, found where a class is compiled from its TASTy as the model is built
  * (`compiled.Compiler`): what it is, and where.
  */
final class NotRead(message: String) extends RuntimeException(message)

object NotRead:
  /** The refusal of `message`, with the file and line of the Scala at `at`. */
  def raise(using q: Quotes)(message: String, at: Option[q.reflect.Tree]): Nothing =
    throw NotRead(message + at.flatMap(place).fold("")(p => s" ($p)"))

  private def place(using q: Quotes)(t: q.reflect.Tree): Option[String] =
    Try(s"${t.pos.sourceFile.name}:${t.pos.startLine + 1}").toOption

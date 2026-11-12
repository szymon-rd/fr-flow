package frflow.dsl.lifted

import dotty.tools.dotc.core.Phases
import dotty.tools.dotc.core.Symbols as Dotc
import scala.quoted.*
import scala.quoted.runtime.impl.QuotesImpl
import scala.util.Try

/** The bodies of a compiled class, read from the TASTy the compiler wrote beside its class file. A compiler started
  * where the model is built (`steps.ReadClass`) knows a class by its signatures until its file's tree is asked
  * for; `load` asks for it, so the members' definitions come with their bodies.
  */
object Tasty:
  /** The tree of the file `member` is written in, loaded whole: after it `member.tree` has its body. */
  def load(q: Quotes)(member: q.reflect.Symbol): Unit = q match
    case compiler: QuotesImpl =>
      import q.reflect.*
      val top = Dotc.toDenot(member.asInstanceOf[Dotc.Symbol])(using compiler.ctx).topLevelClass(using compiler.ctx)
      if top.isClass then
        val root = top.asClass.rootTree(using compiler.ctx)
        (new TreeTraverser {}).traverseTree(root.asInstanceOf[Tree])(Symbol.spliceOwner)
    case _                    => ()

  /** The compiler's view as it is while a file is typed: the reader looks a type's `FrSpec` up among the givens,
    * which the compiler does only then. What is read from TASTy is as the typer left it.
    */
  def typing(q: Quotes): Quotes = q match
    case compiler: QuotesImpl => QuotesImpl()(using compiler.ctx.withPhase(Phases.inliningPhase(using compiler.ctx)))
    case other                => other

/** Scala the reader does not read, found where a class is read from its TASTy as the model is built
  * (`steps.ReadClass`): what it is, and where. Inside a compilation the same is a compile error at the Scala.
  */
final class NotRead(message: String) extends RuntimeException(message)

object NotRead:
  /** The refusal of `message` at `at`: this exception where the reading is `staged`, a compile error where not. */
  def raise(using q: Quotes)(staged: Boolean, message: String, at: Option[q.reflect.Tree]): Nothing =
    import q.reflect.*
    if staged then throw NotRead(message + at.flatMap(place).fold("")(p => s" ($p)"))
    else at.fold(report.errorAndAbort(message))(t => report.errorAndAbort(message, t.pos))

  private def place(using q: Quotes)(t: q.reflect.Tree): Option[String] =
    Try(s"${t.pos.sourceFile.name}:${t.pos.startLine + 1}").toOption

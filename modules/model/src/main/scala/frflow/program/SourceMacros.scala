package frflow
package program

import java.nio.file.{Files, Paths}
import scala.collection.mutable
import scala.quoted.*

private[frflow] object SourceMacros:
  def here(using Quotes): Expr[String] = Expr(relative(quotes.reflect.Position.ofMacroExpansion.sourceFile.path))
  def at(using Quotes): Expr[Int] = Expr(quotes.reflect.Position.ofMacroExpansion.start)

  def text(x: Expr[Any])(using Quotes): Expr[String] = Expr(written(x))

  def sources(xs: Expr[Seq[Any]])(using Quotes): Expr[List[String]] =
    xs match
      case Varargs(es) => Expr(es.map(written).toList)
      case other       => Expr(List(written(other)))

  // Through inline calls the argument arrives wrapped; its own position is the caller's text.
  private def written(e: Expr[Any])(using Quotes): String =
    import quotes.reflect.*
    val t = unwrap(e.asTerm)
    t.pos.sourceCode.filter(_.nonEmpty).orElse {
      scala.util.Try(Files.readString(Paths.get(t.pos.sourceFile.path)).substring(t.pos.start, t.pos.end)).toOption
    }.getOrElse(e.show).trim

  private def unwrap(using q: Quotes)(t: q.reflect.Term): q.reflect.Term =
    import q.reflect.*
    t match
      case Inlined(_, _, b) => unwrap(b)
      case Typed(b, _)      => unwrap(b)
      case Block(Nil, b)    => unwrap(b)
      case _                => t

  /** The source files of the project code an expression refers to: FrFlow's own (package `frflow`) is not the project's. */
  def sourceFiles(e: Expr[Any])(using Quotes): Expr[List[String]] =
    import quotes.reflect.*
    val files = mutable.LinkedHashSet.empty[String]
    def library(s: Symbol): Boolean = s.fullName == "frflow" || s.fullName.startsWith("frflow.")
    def add(s: Symbol): Unit =
      if !s.isNoSymbol && !library(s) then
        s.pos.map(p => Paths.get(p.sourceFile.path)).filter(Files.isRegularFile(_))
          .map(_.toAbsolutePath.normalize.toString).filter(_.endsWith(".scala")).foreach(files += _)
    object T extends TreeTraverser:
      override def traverseTree(t: Tree)(owner: Symbol): Unit =
        t match
          case r: Ref => add(r.symbol); add(r.symbol.owner)
          case n: New => add(n.tpe.typeSymbol)
          case _      => ()
        super.traverseTree(t)(owner)
    T.traverseTree(e.asTerm)(Symbol.spliceOwner)
    add(e.asTerm.tpe.widen.typeSymbol)
    val own = Some(Paths.get(Position.ofMacroExpansion.sourceFile.path).toAbsolutePath.normalize.toString)
    val kept = files.toList.filterNot(f => own.contains(f) && files.size > 1)
    // The model's own file comes last: it is where the implementation is attached, not part of it.
    Expr(kept.map(relative) ++ own.filter(o => !kept.contains(o)).map(relative))

  // Relative to the build's directory, so the paths hold in any checkout.
  private def relative(f: String): String =
    val (base, p) = (Paths.get("").toAbsolutePath.normalize, Paths.get(f).toAbsolutePath.normalize)
    if p.startsWith(base) then base.relativize(p).toString else p.toString

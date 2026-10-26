package frflow
package program

import java.nio.file.{Files, Paths}
import java.util.regex.Pattern
import scala.collection.mutable
import scala.quoted.*

private[frflow] object SourceMacros:
  def here(using Quotes): Expr[String] = Expr(relative(quotes.reflect.Position.ofMacroExpansion.sourceFile.path))
  def at(using Quotes): Expr[Int] = Expr(quotes.reflect.Position.ofMacroExpansion.start)

  def text(x: Expr[Any])(using Quotes): Expr[String] = Expr(written(x))

  def nodeId(using Quotes): Expr[String] = Expr(valName("a node", "Node.claim(\"…\")(…)").capitalize)
  def paramName(using Quotes): Expr[String] = Expr(valName("a Param", "Param[A](\"…\")"))
  def boundaryName(using Quotes): Expr[String] = Expr(valName("a boundary", "Boundary[T](\"…\")"))

  /** The name of the val whose right-hand side the call is: `val name = Node.claim(…)(…).refines(…)`. */
  private[frflow] def valName(what: String, example: String)(using Quotes): String =
    import quotes.reflect.*
    val call = Position.ofMacroExpansion
    def named(s: Symbol): Option[Symbol] =
      if s.isNoSymbol || s.isPackageDef || s.isClassDef then None
      else if s.isValDef && !s.flags.is(Flags.Synthetic) && !s.flags.is(Flags.Param) then Some(s)
      else named(s.owner)
    val name = named(Symbol.spliceOwner).filter { v =>
      val content = call.sourceFile.content.orElse(scala.util.Try(Files.readString(Paths.get(call.sourceFile.path))).toOption)
      val written = s"(?s)(?:(?:private|protected|lazy|override|final)\\s+)*(?:val\\s+)?${Pattern.quote(v.name)}\\s*(?::.*)?=\\s*"
      v.pos.exists(p => content.exists(c => p.start <= call.start && c.substring(p.start, call.start).matches(written)))
    }
    name.map(_.name).getOrElse(report.errorAndAbort(
      s"FrFlow: $what is named by the val it is assigned to: write `val name = $example`", call))

  def sources(xs: Expr[Seq[Any]])(using Quotes): Expr[List[String]] =
    xs match
      case Varargs(es) => Expr(es.map(written).toList)
      case other       => Expr(List(written(other)))

  // Through inline calls the argument arrives wrapped; its own position is the caller's text.
  private def written(e: Expr[Any])(using Quotes): String =
    import quotes.reflect.*
    val t = unwrap(e.asTerm)
    val text = t.pos.sourceCode.filter(_.nonEmpty).orElse {
      scala.util.Try(Files.readString(Paths.get(t.pos.sourceFile.path)).substring(t.pos.start, t.pos.end)).toOption
    }.getOrElse(e.show).trim
    if startsItsLine(t.pos) then dedent(text, t.pos.startColumn) else text

  // A block on lines of its own (after `:`) reads from its first line's column, as a lambda written inline does.
  private def startsItsLine(using q: Quotes)(pos: q.reflect.Position): Boolean =
    val content = pos.sourceFile.content.orElse(scala.util.Try(Files.readString(Paths.get(pos.sourceFile.path))).toOption)
    content.exists(c => c.substring(c.lastIndexOf('\n', pos.start - 1) + 1, pos.start).isBlank)

  private def dedent(text: String, column: Int): String =
    text.linesIterator.zipWithIndex.map((l, i) => if i == 0 then l else l.drop(l.takeWhile(_ == ' ').length.min(column)))
      .mkString("\n")

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

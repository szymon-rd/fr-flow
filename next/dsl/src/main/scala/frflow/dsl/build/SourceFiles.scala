package frflow.dsl.build

import java.nio.file.{Files, Paths}
import scala.collection.mutable
import scala.quoted.*

/** The project's source files plain code is written in, read at compile time: the file of each class, object and
  * method the expression refers to, but FrFlow's own (a library's have no source file on disk). A change to one of
  * them is a change to the code a node governs (the code cause).
  */
object SourceFiles:
  inline def of(inline x: Any): List[String] = ${ filesOf('x) }

  private def filesOf(e: Expr[Any])(using Quotes): Expr[List[String]] =
    import quotes.reflect.*
    val files = mutable.LinkedHashSet.empty[String]
    def library(s: Symbol): Boolean = s.fullName == "frflow" || s.fullName.startsWith("frflow.")
    def add(s: Symbol): Unit =
      if !s.isNoSymbol && !library(s) then
        s.pos.map(p => Paths.get(p.sourceFile.path)).filter(Files.isRegularFile(_))
          .map(_.toAbsolutePath.normalize.toString).filter(_.endsWith(".scala")).foreach(files += _)
    object Refs extends TreeTraverser:
      override def traverseTree(t: Tree)(owner: Symbol): Unit =
        t match
          case r: Ref => add(r.symbol); add(r.symbol.owner)
          case n: New => add(n.tpe.typeSymbol)
          case _      => ()
        super.traverseTree(t)(owner)
    Refs.traverseTree(e.asTerm)(Symbol.spliceOwner)
    Expr(files.toList)

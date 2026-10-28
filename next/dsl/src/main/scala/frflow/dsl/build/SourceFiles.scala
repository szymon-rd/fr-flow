package frflow.dsl.build

import java.nio.file.{Files, Paths}
import scala.collection.mutable
import scala.quoted.*

/** The project's source files plain code is written in, read at compile time: the file of each class, object and
  * method the expression refers to, but FrFlow's own (a library's have no source file on disk) and what the
  * expression defines itself (its lambdas' parameters, its local values: their file is where the code is attached,
  * the FrModel's, not the code's). A change to one of them is a change to the code a node governs (the code cause).
  * The files are looked up on disk by the compiler (`Files.isRegularFile`), so a fingerprint names what was there
  * when the model was compiled.
  */
object SourceFiles:
  inline def of(inline x: Any): List[String] = ${ filesOf('x) }

  private def filesOf(e: Expr[Any])(using Quotes): Expr[List[String]] =
    import quotes.reflect.*
    val files = mutable.LinkedHashSet.empty[String]
    val defined = mutable.Set.empty[Symbol]
    def library(s: Symbol): Boolean = s.fullName == "frflow" || s.fullName.startsWith("frflow.")
    def add(s: Symbol): Unit =
      if !s.isNoSymbol && !library(s) && !defined(s) then
        s.pos.map(p => Paths.get(p.sourceFile.path)).filter(Files.isRegularFile(_))
          .map(_.toAbsolutePath.normalize.toString).filter(_.endsWith(".scala")).foreach(files += _)
    object Defs extends TreeTraverser:
      override def traverseTree(t: Tree)(owner: Symbol): Unit =
        t match
          case d: Definition => defined += d.symbol
          case b: Bind       => defined += b.symbol
          case _             => ()
        super.traverseTree(t)(owner)
    object Refs extends TreeTraverser:
      override def traverseTree(t: Tree)(owner: Symbol): Unit =
        t match
          case r: Ref if !defined(r.symbol) => add(r.symbol); add(r.symbol.owner)
          case n: New                       => add(n.tpe.typeSymbol)
          case _                            => ()
        super.traverseTree(t)(owner)
    Defs.traverseTree(e.asTerm)(Symbol.spliceOwner)
    Refs.traverseTree(e.asTerm)(Symbol.spliceOwner)
    Expr(files.toList)

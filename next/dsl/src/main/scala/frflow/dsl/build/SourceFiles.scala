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

  private def filesOf(e: Expr[Any])(using q: Quotes): Expr[List[String]] =
    import q.reflect.*
    val inside = defined(e.asTerm)
    Expr(referred(e.asTerm, inside).filterNot(inside).flatMap(file).distinct)

  /** What the expression defines itself: its definitions and its patterns' bindings. */
  private def defined(using q: Quotes)(t: q.reflect.Term): Set[q.reflect.Symbol] =
    import q.reflect.*
    val found = mutable.Set.empty[Symbol]
    object Defs extends TreeTraverser:
      override def traverseTree(t: Tree)(owner: Symbol): Unit =
        t match
          case d: Definition => found += d.symbol: Unit
          case b: Bind       => found += b.symbol: Unit
          case _             => ()
        super.traverseTree(t)(owner)
    Defs.traverseTree(t)(Symbol.spliceOwner)
    found.toSet

  /** Each symbol defined outside the expression it refers to, with its owner, and each class it makes, in the order
    * met.
    */
  private def referred(using q: Quotes)(t: q.reflect.Term, inside: Set[q.reflect.Symbol]): List[q.reflect.Symbol] =
    import q.reflect.*
    val found = mutable.ListBuffer.empty[Symbol]
    object Refs extends TreeTraverser:
      override def traverseTree(t: Tree)(owner: Symbol): Unit =
        t match
          case r: Ref if !inside(r.symbol) => found ++= List(r.symbol, r.symbol.owner): Unit
          case n: New                      => found += n.tpe.typeSymbol: Unit
          case _                           => ()
        super.traverseTree(t)(owner)
    Refs.traverseTree(t)(Symbol.spliceOwner)
    found.toList

  /** The Scala file on disk a symbol is written in, but FrFlow's own. */
  private def file(using q: Quotes)(s: q.reflect.Symbol): Option[String] =
    val library = s.fullName == "frflow" || s.fullName.startsWith("frflow.")
    Option.when(!s.isNoSymbol && !library)(s.pos).flatten.map(p => Paths.get(p.sourceFile.path))
      .filter(Files.isRegularFile(_)).map(_.toAbsolutePath.normalize.toString).filter(_.endsWith(".scala"))

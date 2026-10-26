package frflow.dsl.build

import scala.quoted.*

/** What the compiler knows of a model's parts at the call site: where they are written, their text, a lambda's
  * parameter names, and the name of the `val` a define is assigned to. Read at compile time, so elaboration needs no
  * reflection on the developer's lambdas but to find what a flow's lambda captures (`Captures`).
  */
object Source:
  inline def of(inline x: Any): AsWritten = ${ writtenOf('x) }
  inline def file: String = ${ fileOf }
  inline def offset: Int = ${ offsetOf }
  /** The name of the `val` the expression is the right-hand side of: `val matches = define { … }` gives `matches`. */
  inline def valName: String = ${ valNameOf }

  private def writtenOf(x: Expr[Any])(using Quotes): Expr[AsWritten] =
    import quotes.reflect.*
    val text = x.asTerm.pos.sourceCode.getOrElse(x.show).trim
    '{ AsWritten(${ Expr(text) }, ${ Expr(params(x)) }) }

  /** A lambda's parameter names; none for an expression that is not a lambda. */
  private def params(x: Expr[Any])(using Quotes): List[String] =
    import quotes.reflect.*
    def go(t: Term): List[String] = t match
      case Inlined(_, _, body)                      => go(body)
      case Typed(body, _)                           => go(body)
      case Block(List(DefDef(_, List(ps), _, _)), _) => ps.params.map(_.name)
      case Block(Nil, body)                         => go(body)
      case _                                        => Nil
    go(x.asTerm)

  private def fileOf(using Quotes): Expr[String] =
    Expr(quotes.reflect.Position.ofMacroExpansion.sourceFile.path)
  private def offsetOf(using Quotes): Expr[Int] =
    Expr(quotes.reflect.Position.ofMacroExpansion.start)
  private def valNameOf(using Quotes): Expr[String] =
    import quotes.reflect.*
    def owner(s: Symbol): Symbol = if s.isValDef && !s.flags.is(Flags.Synthetic) then s else owner(s.owner)
    Expr(owner(Symbol.spliceOwner).name)

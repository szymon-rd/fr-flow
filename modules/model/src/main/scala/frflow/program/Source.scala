package frflow
package program

import scala.quoted.*

/** Where a model's parts are written, and their text as written: what the developer reads and decides. Nothing
  * here translates anything; the Lean comes from the terms themselves.
  */
object Source:
  /** The source file of the call site. */
  inline def here: String = ${ SourceMacros.here }
  inline def at: Int = ${ SourceMacros.at }
  /** The text of an expression, as written. */
  inline def text(inline x: Any): String = ${ SourceMacros.text('x) }
  inline def sources(inline xs: Any*): List[String] = ${ SourceMacros.sources('xs) }
  /** The project's source files an expression refers to (an implementation's code, say). */
  inline def sourceFiles(inline x: Any): List[String] = ${ SourceMacros.sourceFiles('x) }

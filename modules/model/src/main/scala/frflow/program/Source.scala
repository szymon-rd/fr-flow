package frflow
package program

import scala.quoted.*

/** Where a model's parts are written, and their text as written: what the developer reads and decides. The Lean
  * is printed from the terms.
  */
object Source:
  /** The source file of the call site. */
  inline def here: String = ${ SourceMacros.here }
  inline def at: Int = ${ SourceMacros.at }
  /** A node's id: the name of the val it is assigned to, its first letter capitalised (`grantWhenFree`: `GrantWhenFree`). */
  inline def nodeId: String = ${ SourceMacros.nodeId }
  /** A Param's name: the name of the val it is assigned to. */
  inline def paramName: String = ${ SourceMacros.paramName }
  /** A boundary's name: the name of the val it is assigned to. */
  inline def boundaryName: String = ${ SourceMacros.boundaryName }
  /** The text of an expression, as written. */
  inline def text(inline x: Any): String = ${ SourceMacros.text('x) }
  inline def sources(inline xs: Any*): List[String] = ${ SourceMacros.sources('xs) }
  /** The project's source files an expression refers to (an implementation's code, say). */
  inline def sourceFiles(inline x: Any): List[String] = ${ SourceMacros.sourceFiles('x) }

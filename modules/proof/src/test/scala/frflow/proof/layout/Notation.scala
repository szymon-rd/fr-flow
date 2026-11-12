package frflow.proof.layout

import frflow.proof.lean.ast.LeanModule
import frflow.proof.lean.term.PrintDecl

/** A generated module's declarations in the notation a node's content is written in: what the suites read a
  * statement off.
  */
object Notation:
  def module(m: LeanModule): String = m.decls.map(PrintDecl(_)).mkString("\n\n")

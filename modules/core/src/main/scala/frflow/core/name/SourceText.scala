package frflow.core.name

/** Scala as the developer wrote it (a formula, a post, a define's body), taken by a macro at the call site: what the
  * developer reads and decides. It is never parsed or printed as Lean; Lean comes from the elaborated IR.
  */
opaque type SourceText = String

object SourceText:
  def apply(s: String): SourceText = s
  extension (t: SourceText) def value: String = t

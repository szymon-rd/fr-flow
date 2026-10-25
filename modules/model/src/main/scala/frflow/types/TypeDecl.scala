package frflow
package types

final case class TypeDecl(name: String, lean: String, uses: List[String], scala: String = "", ctors: List[(String, List[(String, String)])] = Nil):
  /** Without its doc comment: a file compiled on its own may not see the comment. */
  def body: String = if lean.startsWith("/--") then lean.drop(lean.indexOf("-/\n") + 3) else lean

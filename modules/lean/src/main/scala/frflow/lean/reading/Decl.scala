package frflow
package lean
package reading

final case class Decl(name: String, statement: String, from: Int, to: Int):
  def spans(line: Int): Boolean = line >= from && line <= to

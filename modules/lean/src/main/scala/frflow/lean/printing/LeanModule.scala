package frflow
package lean
package printing

final case class LeanModule(name: String):
  def path: String = name.replace('.', '/') + ".lean"

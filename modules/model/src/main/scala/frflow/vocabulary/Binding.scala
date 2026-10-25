package frflow
package vocabulary

final case class Binding(param: Param[?], value: () => Any, table: Option[Map[?, ?]] = None)

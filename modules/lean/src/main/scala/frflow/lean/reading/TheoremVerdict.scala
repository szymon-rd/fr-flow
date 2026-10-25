package frflow
package lean
package reading

/** Whether Lean proved a theorem of a file. */
enum TheoremVerdict:
  case Proven, Missing
  case Failed(message: String)
  case UsesSorry

  def proven: Boolean = this == Proven
  def why(name: String): Option[String] = this match
    case Proven          => None
    case Missing         => Some(s"no theorem $name")
    case Failed(message) => Some(message)
    case UsesSorry       => Some("uses sorry")

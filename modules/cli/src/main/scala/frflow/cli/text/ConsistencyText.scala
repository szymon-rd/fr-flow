package frflow.cli
package text

import frflow.protocol.*
import frflow.protocol.snapshot.Consistency

/** What `check` says of the FrModel as a whole: its statements hold together, and nothing is vacuous. */
object ConsistencyText:
  def lines(c: Option[Consistency], st: Style): List[String] = c.toList.flatMap(_.items).map { i =>
    val glyph = if i.status == ObligationStatus.Proven then st.proven else st.open
    val said = if i.status == ObligationStatus.Proven then shown(i) else i.detail
    s"$glyph ${st.bold(what(i))}: $said"
  }

  /** The item in a few words: `consistency of GrantWhenNoOverlap`, `EndsAfterStart admits a value`. */
  def what(i: Consistency.Item): String =
    val about = i.about.map(_.value).mkString(", ")
    i.kind match
      case Consistency.Kind.Together  => s"consistency of $about"
      case Consistency.Kind.Admits    => s"$about admits a value"
      case Consistency.Kind.Starts    => s"$about: some state meets it"
      case Consistency.Kind.Condition => s"$about: its condition is met"

  private def shown(i: Consistency.Item): String = i.kind match
    case Consistency.Kind.Together  =>
      s"Lean proves a meaning meets ${if i.about.size == 1 then "it" else "them all"}: ${i.witness}"
    case Consistency.Kind.Admits    => s"Lean proves it holds of ${i.witness.split(" or ").headOption.getOrElse("")}"
    case Consistency.Kind.Starts    => s"Lean proves ${i.witness.split(" or ").headOption.getOrElse("")} meets it"
    case Consistency.Kind.Condition => s"Lean proves ${i.witness} meets it"

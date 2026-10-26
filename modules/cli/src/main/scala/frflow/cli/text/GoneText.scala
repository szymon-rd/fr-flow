package frflow.cli
package text

import frflow.api.*
import frflow.protocol.*

/** A decided node gone from the model, as `show` and `diff` print it: what it said, and its last decision. */
object GoneText:
  def lines(g: GoneNode, st: Style): List[String] =
    val d = g.gone.decision
    val room = st.width.fold(Int.MaxValue)(_ - 2)
    val id = g.gone.id
    (s"${st.red(st.dot)} ${st.bold(id.value)}  ${st.red("gone from the model")}" ::
      st.wrap(d.content.statement, room).map("  " + _) ++ Lines.why(d.content, room, st)) ++
      Lines.section("Decision", Lines.para(s"last ${Words.verb(d.action)} by ${d.by} (${Words.date(d.at)}): ${d.reason}", st) ++
        Lines.para(s"${what(g)}: gone $id agrees that it is gone", st), st)

  /** "renamed to Y" when a node in the model says the same. */
  def what(g: GoneNode): String = g.renamedTo.fold("it is no longer in the model")(y => s"renamed to $y (it says the same)")

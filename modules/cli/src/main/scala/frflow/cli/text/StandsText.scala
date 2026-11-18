package frflow.cli.text

import frflow.api.view.{View, Views}
import frflow.cli.term.Style
import frflow.core.name.NodeId

/** What a node stands on at the bottom (`stands`): the assumptions it is proven from, each in a line, and the claims
  * below it that are not proven for a reason of their own.
  */
object StandsText:
  def of(v: View, id: NodeId, st: Style): List[String] =
    val on = Views.standsOn(v, id)
    val proven = if on.unproven.isEmpty then "and on nothing that is not proven"
      else s"and on ${on.unproven.size} claim(s) not proven"
    List(Lines.of(v, id, st), st.dim(s"  stands on ${on.assumed.size} assumption(s), $proven")) ++
      on.assumed.map(a => "  " + Lines.of(v, a, st, 2)) ++
      Lines.section("Not proven, for a reason of its own", on.unproven.map(Lines.of(v, _, st, 2)), st)

  /** Of each root, in the author's order. */
  def roots(v: View, st: Style): List[String] =
    v.roots.map(of(v, _, st)).flatMap(_ :+ "").dropRight(1)

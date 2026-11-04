package frflow.cli.text

import frflow.api.view.{View, Views}
import frflow.cli.say.Warnings
import frflow.cli.term.Style
import frflow.core.name.NodeId

/** The DAG drawn as a tree (`tree`), and `status`: the tree, the warnings, the summary. `marks`: a word a layer on top
  * shows beside a node.
  */
object TreeText:
  def lines(v: View, from: Option[NodeId], st: Style, marks: Map[NodeId, String]): List[String] =
    Views.tree(v, from).flatMap((depth, id) => v.node(id).map { n =>
      val mark = marks.get(id).fold("")(m => "  " + st.magenta(m))
      st.fit("  " * depth + Lines.node(n, st.copy(width = None)) + mark)
    })

  /** What `status` prints: the tree, each warning (FrFlow's, then the layers'), the summary. */
  def status(v: View, st: Style, layers: Contribution): List[String] =
    lines(v, None, st, layers.marks) ++ warnings(v, layers.warnings, st) ++
      ("" :: SummaryText.lines(v, InboxText.waiting(v, layers.aside), st, layers.waiting))

  def warnings(v: View, more: List[String], st: Style): List[String] =
    (v.warnings.map(Warnings.text) ++ more).flatMap(w => Lines.para(st.red(s"warning: $w"), st, indent = 0))

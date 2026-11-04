package frflow.cli.text

import frflow.api.node.NodeView
import frflow.api.view.View
import frflow.cli.say.Refusals
import frflow.cli.term.{Marks, Style}
import frflow.core.name.NodeId
import frflow.core.spec.NodeKind

/** The pieces every view is printed with: a node in one line, a titled section, a paragraph wrapped to the width. */
object Lines:
  /** `✓ nonNegative  claim  accepted  The service never gives…`, cut to the width less `indent`. */
  def node(n: NodeView, st: Style, indent: Int = 0): String =
    st.fit(s"${Marks.glyph(n, st)} ${st.bold(n.id.value)}  ${st.dim(kind(n.says.kind))}  " +
      s"${Marks.state(n.review.standing.state, Refusals.state(n.review.standing.state), st)}  ${statement(n)}", indent)

  /** A node of the view in one line, or its id when the view has none. */
  def of(v: View, id: NodeId, st: Style, indent: Int = 0): String = v.node(id).fold(id.value)(node(_, st, indent))

  def kind(k: NodeKind): String = k match
    case NodeKind.Claim      => "claim"
    case NodeKind.Assumption => "assumption"
    case NodeKind.Design     => "design"

  /** Its sentence on one line, whatever spaces it was written with. */
  def statement(n: NodeView): String = n.says.statement.replaceAll("\\s+", " ").trim

  /** A title and its lines indented by two; nothing when there are no lines. */
  def section(title: String, lines: List[String], st: Style): List[String] =
    if lines.isEmpty then Nil else "" :: st.bold(title) :: lines.map("  " + _)

  /** `text` wrapped to the width less `indent`, its later lines under its first by `hang`. */
  def para(text: String, st: Style, indent: Int = 2, hang: Int = 2): List[String] =
    st.width.fold(List(text)) { w =>
      st.wrap(text, (w - indent).max(20)) match
        case first :: rest => first :: rest.map(" " * hang + _)
        case Nil           => Nil
    }

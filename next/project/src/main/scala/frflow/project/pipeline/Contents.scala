package frflow.project.pipeline

import frflow.core.analysis.Resolved
import frflow.core.graph.Edge
import frflow.core.name.NodeId
import frflow.core.spec.{CallForm, FailureClause, Node, Reliance, Statement}
import frflow.decision.content.{Content, FieldValue}
import frflow.proof.lean.lower.LowerType
import frflow.proof.lean.print.Print

/** A node's decided form: what it says (its sentence and formula; its reason is its decision's), where it sits, and
  * how it is checked. One form, FrFlow's own: the ledgers start fresh with it, so no older form is read. The rebuilt
  * examples' goldens pin every node's content.
  */
object Contents:
  def of(r: Resolved, id: NodeId): Content =
    r.theory.node(id).fold(Content.empty)(n => Content(said(r, n) ++ done(r, n)))

  /** What the node says. */
  private def said(r: Resolved, n: Node): List[(String, FieldValue)] = List(
    Some("kind" -> text(n.statement.kind.toString.toLowerCase)),
    Some("parents" -> texts(r.theory.refinement.parents(n.id).map(_.value))),
    Option.when(n.statement.stated)("parts" -> texts(r.theory.refinement.parts(n.id).map(_.value))),
    Some("assumes" -> texts(r.theory.refinement.assumed(n.id).map(_.value))),
    Some("statement" -> text(n.says)),
    n.statement.said.map(f => "formula" -> text(f.source.value)),
    Some("vocabulary" -> texts(Texts.vocabulary(r.theory, n.id)))).flatten

  /** How it is checked and how its code stands. */
  private def done(r: Resolved, n: Node): List[(String, FieldValue)] = List(
    Some("checking" -> texts(Texts.checking(r.theory, n.id))),
    Some("governs" -> texts(governs(n.statement))),
    n.statement.definition.map(o => "call" -> text(o.value)),
    r.theory.edges.collectFirst { case Edge.Replaces(a, o) if a == n.id => "replaces" -> text(o.value) },
    Option.when(n.statement.relied == Reliance.LeftOpen)("reliance" -> text("left open above")),
    failure(n.statement).map("failure" -> text(_)),
    CodeTexts.implementation(r, n.id).map("implementation" -> text(_)),
    CodeTexts.model(r, n.id).map("model" -> texts(_)),
    CodeTexts.implementations(r, n.id).map("implementations" -> texts(_))).flatten

  private def governs(s: Statement): List[String] = s match
    case Statement.Design(gs) => gs.toList.map(_.value)
    case _                    => Nil

  private def failure(s: Statement): Option[String] = s.call.collect {
    case CallForm.Run(_, _, Some(FailureClause(e, post))) =>
      s"fails with ${Print.expr(LowerType(e))}: ${post.source.value}"
  }

  private def text(s: String): FieldValue = FieldValue.Text(s)
  private def texts(ss: List[String]): FieldValue = FieldValue.Texts(ss)

package frflow.project.pipeline

import frflow.core.analysis.{Premises, Resolved, Scope}
import frflow.core.graph.Edge
import frflow.core.name.NodeId
import frflow.core.spec.{CallForm, FailureClause, Node, Reliance, Statement, Written}
import frflow.decision.content.{Content, FieldValue}
import frflow.proof.lean.lower.LowerType
import frflow.core.expr.{Expr, Exprs}
import frflow.proof.layout.{Lowering, VocabularyModules}
import frflow.proof.lean.print.{Print, PrintDecl}
import frflow.proof.lean.term.Printed

/** A node's decided form: what it says (its sentence and formula; its reason is its decision's), where it sits, and
  * how it is checked. Its `formula` is what the formula means: the elaborated term as Lean is given it (FrFlow's
  * defines by name, a variable by its place), so a helper whose body changes moves it, and wording the Scala
  * differently does not; `written` is the Scala as the developer wrote it, shown, not part of the meaning
  * (`Meaning`). One form, FrFlow's own: the ledgers start fresh with it, so no older form is read. The rebuilt
  * examples' goldens pin every node's content.
  */
object Contents:
  def of(l: Lowering, id: NodeId): Content =
    val r = l.resolved
    r.theory.node(id).fold(Content.empty)(n => Content(said(l, n) ++ done(r, n)))

  /** What the node says. */
  private def said(l: Lowering, n: Node): List[(String, FieldValue)] =
    val r = l.resolved
    List(
      Some("kind" -> text(n.statement.kind.toString.toLowerCase)),
      Some("parents" -> texts(r.theory.refinement.parents(n.id).map(_.value))),
      Option.when(n.statement.stated)("parts" -> texts(r.theory.refinement.parts(n.id).map(_.value))),
      Some("assumes" -> texts(r.theory.refinement.assumed(n.id).map(_.value))),
      Some("statement" -> text(n.says)),
      n.statement.said.map(f => "formula" -> text(meaning(l, f))),
      n.statement.said.map(f => "written" -> text(f.source.value)),
      Some("vocabulary" -> texts(Texts.vocabulary(r.theory, n.id)))).flatten

  /** A formula as Lean is given it, then each define it calls, however far, as Lean is given it: `l` canonical, its
    * variables named by the order they are bound (`Analysis.canonical`).
    */
  private def meaning(l: Lowering, f: Written[Expr]): String =
    val defines = l.resolved.theory.vocabulary.closure(Exprs.mentions(f.value).defines)
    (Print.expr(Printed.formula(l.env, l.naming)(f.term)) :: defines.map(d =>
      PrintDecl(VocabularyModules.declared(l, d)))).mkString("\n\n")

  /** How it is checked and how its code stands. */
  private def done(r: Resolved, n: Node): List[(String, FieldValue)] = List(
    Some("checking" -> texts(Texts.checking(r.theory, n.id))),
    writers(r, n).map("writers" -> texts(_)),
    Some("governs" -> texts(governs(n.statement))),
    n.statement.definition.map(o => "call" -> text(o.value)),
    r.theory.edges.collectFirst { case Edge.Replaces(a, o) if a == n.id => "replaces" -> text(o.value) },
    Option.when(n.statement.relied == Reliance.LeftOpen)("reliance" -> text("left open above")),
    failure(n.statement).map("failure" -> text(_)),
    CodeTexts.implementation(r, n.id).map("implementation" -> text(_)),
    CodeTexts.model(r, n.id).map("model" -> texts(_)),
    CodeTexts.implementations(r, n.id).map("implementations" -> texts(_))).flatten

  /** Of a rule about a store, the programs changing the store, derived (owner §31): one added brings it back. */
  private def writers(r: Resolved, n: Node): Option[List[String]] =
    val models = n.statement.range.filter(_ => n.statement.rule).toList.flatMap(Scope.models(r.theory, _))
    Option.when(models.nonEmpty)(models.flatMap(Premises.writers(r.theory, _)).map(_.value).distinct)

  private def governs(s: Statement): List[String] = s match
    case Statement.Design(gs) => gs.toList.map(_.value)
    case _                    => Nil

  private def failure(s: Statement): Option[String] = s.call.collect {
    case CallForm.Run(_, _, Some(FailureClause(e, post))) =>
      s"fails with ${Print.expr(LowerType(e))}: ${post.source.value}"
  }

  private def text(s: String): FieldValue = FieldValue.Text(s)
  private def texts(ss: List[String]): FieldValue = FieldValue.Texts(ss)

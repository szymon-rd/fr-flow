package frflow.project.report

import frflow.core.analysis.Scope
import frflow.core.checking.Shown
import frflow.core.consistency.{Consistency, Group}
import frflow.core.name.NodeId
import frflow.core.spec.{NodeKind, Statement}
import frflow.decision.review.Subject
import frflow.project.pipeline.{Analysis, Texts}
import frflow.proof.layout.Composition
import frflow.proof.lean.print.Print
import frflow.proof.obligation.ObligationName
import frflow.proof.verdict.Result
import frflow.wire.snapshot.*

/** The snapshot (`.frflow/kb.json`) of an analysis: the nodes in decision order, each with its content as decided,
  * its place, its current check with each obligation's Lean statement, and how it is checked and tested; beside
  * them the consistency groups and the examples as checked. Made by `wire`'s rows (`Rows`) only.
  */
object Exports:
  def snapshot(a: Analysis): Snapshot =
    val t = a.decided.theory
    Snapshot(t.name.value, t.refinement.roots.map(_.id.value),
      t.refinement.nodes.filter(_.statement.kind == NodeKind.Assumption).map(_.id.value),
      (t.vocabulary.sorts.map(s => TermRow(s.name.value, s.means)) ++
        t.vocabulary.symbols.map(s => TermRow(s.name.value, s.means))).sortBy(_.name),
      a.subjects.inOrder.map(node(a, _)),
      Consistency.of(t).collect { case g: Group.Sharing => Rows.group(g) },
      a.computed.examples.zipWithIndex.map { case ((e, onCode), i) =>
        Rows.example(e, a.wholeCheck.flatMap(_.results.find(_.name == ObligationName.Example(i))).map(_.status), onCode)
      })

  private def node(a: Analysis, s: Subject): SnapNode =
    val r = a.decided
    val g = r.theory.refinement
    SnapNode(Header(s.id.value, s.place.kind.toString.toLowerCase, s.content.hash.value, Rows.content(s.content)),
      PlaceRow(g.parents(s.id).map(_.value), g.parts(s.id).map(_.value), g.assumed(s.id).map(_.value),
        r.reliesOn(s.id).map(_.value), Scope.of(r.theory, s.id).map(_.value)),
      check(a, s.id), body(a, s.id))

  private def check(a: Analysis, id: NodeId): CheckRow =
    val c = a.current(id)
    val composition = Composition(a.lowering)
    val holds = Option.when(composition.composed(id))(Print.expr(a.lowering.props.statement(composition.holds(id))))
    CheckRow(c.fold("unchecked")(_.status.toString.toLowerCase), holds.getOrElse(""),
      c.toList.flatMap(_.results).map(x => Rows.obligation(x, statement(a, id, x))))

  /** An obligation's statement, as Lean is given it. */
  private def statement(a: Analysis, id: NodeId, r: Result): String =
    a.obligations.find(_.node == id).toList.flatMap(o => o.required ++ o.tried).find(_.name == r.name)
      .fold("")(o => Print.expr(a.lowering.props.statement(o.goal)))

  private def body(a: Analysis, id: NodeId): Body = a.decided.theory.node(id).map(_.statement) match
    case Some(Statement.Design(gs)) => Body.Design(gs.toList.map(_.value))
    case statement                  =>
      val shown = Shown.of(a.decided.theory, id)
      val coded = shown.proven.nonEmpty || shown.tested.nonEmpty || shown.assumed.nonEmpty
      Body.Stated(Texts.checking(a.decided.theory, id), statement.flatMap(_.definition).map(_.value),
        Option.when(coded)(Rows.code(shown)), a.tested(id).map(Rows.test))

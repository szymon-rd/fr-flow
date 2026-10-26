package frflow.project.pipeline

import frflow.core.analysis.Resolved
import frflow.core.graph.Edge
import frflow.core.name.NodeId
import frflow.core.spec.{FailureClause, Fixing, Node, NodeKind, Promise, Reliance, Statement}
import frflow.decision.content.{Content, FieldValue}
import frflow.proof.lean.lower.LowerType
import frflow.proof.lean.print.Print

/** A node's decided form, `V2`: today's fields in today's order and with today's texts, less the retired ones
  * (`definition`, the idea's), and with `reliance` and `failure`, the two facts only `definition` held. A stored
  * format: the step-0 golden pins every example node's content.
  */
object Contents:
  def of(r: Resolved, id: NodeId): Content =
    r.theory.node(id).fold(Content.empty)(n => Content(said(r, n) ++ done(r, n)))

  /** What the node says. */
  private def said(r: Resolved, n: Node): List[(String, FieldValue)] = List(
    Some("kind" -> text(kind(n.statement.kind))),
    Some("parents" -> texts(r.theory.refinement.parents(n.id).map(_.value))),
    Option.when(n.statement.stated)("parts" -> texts(r.theory.refinement.parts(n.id).map(_.value))),
    Some("statement" -> text(n.prose.statement)),
    Some("why" -> text(n.prose.why)),
    Some("sources" -> FieldValue.Record(sources(n.statement))),
    Some("substitutions" -> texts(substitutions(n.statement))),
    Some("examples" -> texts(Texts.examples(n.statement))),
    Some("vocabulary" -> texts(Texts.vocabulary(r.theory, n.id))),
    Some("uses" -> texts(Texts.uses(r, n.id)))).flatten

  /** What it is about and how its code stands. */
  private def done(r: Resolved, n: Node): List[(String, FieldValue)] = List(
    Some("governs" -> texts(governs(n.statement))),
    n.statement.operation.map(o => "op" -> text(o.value)),
    r.theory.edges.collectFirst { case Edge.Replaces(a, o) if a == n.id => "replaces" -> text(o.value) },
    Option(Texts.keeps(r, n.id)).filter(_.nonEmpty).map("keeps" -> texts(_)),
    Option(expects(n.statement)).filter(_.nonEmpty).map("expects" -> texts(_)),
    reliance(n.statement).map("reliance" -> text(_)),
    failure(n.statement).map("failure" -> text(_)),
    Texts.implementation(r, n.id).map("implementation" -> text(_)),
    Texts.model(r, n.id).map("model" -> texts(_)),
    Texts.implementations(r, n.id).map("implementations" -> texts(_)),
    r.theory.code.attached.get(n.id).flatMap(_.runCheck).map(c => "runtime" -> text(Texts.runCheck(c)))).flatten

  /** As today's `NodeKind`: an invariant is a claim with a rule. */
  private def kind(k: NodeKind): String = if k == NodeKind.Invariant then "claim" else k.toString.toLowerCase

  private def sources(s: Statement): List[(String, String)] = s match
    case Statement.Claim(f, _)                => List("formula" -> f.source.value)
    case Statement.Fact(f)                    => List("formula" -> f.source.value)
    case Statement.Invariant(rule, _)         => List("rule" -> rule.source.value)
    case Statement.Contract(_, p, _)          => promise(p)
    case Statement.FlowContract(_, p, _, _)   => promise(p)
    case Statement.AssumedCall(_, p)          => promise(p)
    case Statement.Model(_) | Statement.Definition(_) | Statement.Design(_) => Nil

  private def promise(p: Promise[?]): List[(String, String)] =
    ("post" -> p.post.source.value) :: p.check.map("check" -> _.source.value).toList

  private def substitutions(s: Statement): List[String] = s match
    case Statement.Definition(fs) => fs.toList.map {
      case Fixing.TypeAs(sort, ty) => s"${sort.value} := ${Print.expr(LowerType(ty))}"
      case Fixing.TermAs(sym, as)  => s"${sym.value} := ${as.source.value}"
    }
    case _ => Nil

  private def governs(s: Statement): List[String] = s match
    case Statement.Design(gs) => gs.toList.map(_.value)
    case _                    => Nil

  private def expects(s: Statement): List[String] = s match
    case Statement.Claim(_, es) => es.map(e => s"${e.statement}: ${e.consequence.source.value}")
    case _                      => Nil

  private def reliance(s: Statement): Option[String] = s match
    case Statement.Contract(_, _, Reliance.LeftOpen) | Statement.FlowContract(_, _, _, Reliance.LeftOpen) =>
      Some("left open above")
    case _ => None

  private def failure(s: Statement): Option[String] = s match
    case Statement.FlowContract(_, _, Some(FailureClause.ChangesNothing(e)), _) =>
      Some(s"fails with ${Print.expr(LowerType(e))}, changing nothing")
    case Statement.FlowContract(_, _, Some(FailureClause.Holds(e, post)), _)    =>
      Some(s"fails with ${Print.expr(LowerType(e))}: ${post.source.value}")
    case _ => None

  private def text(s: String): FieldValue = FieldValue.Text(s)
  private def texts(ss: List[String]): FieldValue = FieldValue.Texts(ss)

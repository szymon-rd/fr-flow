package frflow.project.pipeline

import cats.syntax.all.*
import frflow.core.analysis.{Constrained, Resolved}
import frflow.core.code.{Code, Realizes}
import frflow.core.expr.OutsideFact
import frflow.core.name.NodeId
import frflow.core.Theory
import frflow.proof.layout.Lowering
import frflow.proof.lean.lower.LowerModels
import frflow.proof.lean.print.PrintDecl
import frflow.proof.terms.TermTable
import frflow.wire.snapshot.Rows

/** The content fields of the code: what gives each Definition a statement mentions its meaning, and of a store said
  * to behave as its model, the model (as Lean reads it) and the implementations tested against it.
  */
object CodeTexts:
  /** One line per Definition it mentions that has a meaning, sorted: the define's or the program's source, the plain
    * Scala's expression, the value fixed, or that it is provided where the code runs.
    */
  def implementation(r: Resolved, id: NodeId): Option[String] =
    val t = r.theory
    Option(Constrained.of(t, id).sortBy(_.value).flatMap(s => t.code.attached.get(s).map(a =>
      s"${s.value}: ${coded(t, a.code)}"))).filter(_.nonEmpty).map(_.mkString("\n"))

  /** Of an assumption that a store behaves as its model: the model's operations, as Lean is given them. */
  def model(r: Resolved, id: NodeId): Option[List[String]] = modelled(r.theory, id).flatMap { (b, m) =>
    val v = r.theory.vocabulary
    (v.boundary(b), v.model(m)).mapN { (sig, model) =>
      val l = Lowering(r, TermTable.of(r))
      PrintDecl(LowerModels(l.env, l.naming).model(sig, model)).linesIterator.toList
    }
  }

  /** Of the same assumption: each implementation run against the model, whose it is, and its expression. */
  def implementations(r: Resolved, id: NodeId): Option[List[String]] = modelled(r.theory, id).flatMap((b, _) =>
    r.theory.code.realized.get(b).map(_.toList.map(x => s"${whose(x.how)}: ${x.runs.written.value}")))

  private def modelled(t: Theory, id: NodeId) = t.node(id).flatMap(_.statement.outside).collect {
    case OutsideFact.BehavesAs(b, m) => (b, m)
  }

  private def coded(t: Theory, c: Code): String = c match
    case Code.Proven(d)       => s"proven, ${t.vocabulary.define(d).fold(d.value)(_.written.source.value)}"
    case Code.ProvenFlow(f)   => s"proven program, ${t.vocabulary.define(f).fold(f.value)(_.written.source.value)}"
    case Code.Tested(runs, _) => s"Scala, ${runs.written.value}"
    case Code.Valued(v)       => s"the value ${Rows.shown(v)}"
    case Code.Provided        => "provided where the code runs"

  private def whose(r: Realizes): String = r match
    case Realizes.Own     => "the project's own"
    case Realizes.Outside => "an outside system's"

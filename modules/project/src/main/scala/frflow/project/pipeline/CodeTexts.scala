package frflow.project.pipeline

import frflow.core.analysis.{Constrained, Resolved}
import frflow.core.code.Code
import frflow.core.expr.OutsideFact
import frflow.core.name.{ModelName, NodeId}
import frflow.core.Theory
import frflow.proof.layout.Lowering
import frflow.proof.lean.lower.LowerModels
import frflow.proof.lean.print.PrintDecl
import frflow.proof.terms.TermTable
import frflow.wire.snapshot.Rows

/** The content fields of the code: what gives each Definition a statement mentions its meaning, and of the
  * assumption that only the code changes a model's state (what its model tests are reported under), the model as
  * Lean reads it and its operations' Scala tested against it.
  */
object CodeTexts:
  /** One line per Definition it mentions that has a meaning, sorted: the define's or the program's source, the plain
    * Scala's expression, the value fixed, or that it is provided where the code runs.
    */
  def implementation(r: Resolved, id: NodeId): Option[String] =
    val t = r.theory
    Option(Constrained.of(t, id).sortBy(_.value).flatMap(s => t.code.attached.get(s).map(a =>
      s"${s.value}: ${coded(t, a.code)}"))).filter(_.nonEmpty).map(_.mkString("\n"))

  /** Of the assumption that only the code changes a model's state: the model's operations, as Lean is given them. */
  def model(r: Resolved, id: NodeId): Option[List[String]] = modelled(r.theory, id).flatMap(lean(r, _))

  /** A model's operations, as Lean is given them. */
  def lean(r: Resolved, m: ModelName): Option[List[String]] = r.theory.vocabulary.model(m).map { model =>
    val l = Lowering(r, TermTable.of(r))
    PrintDecl(LowerModels(l.env, l.naming).model(model)).linesIterator.toList
  }

  /** Of the same assumption: the Scala of the model's operations tested against it, as written. */
  def implementations(r: Resolved, id: NodeId): Option[List[String]] = modelled(r.theory, id)
    .flatMap(r.theory.code.implemented.get).map(i => List(i.written.value))

  private def modelled(t: Theory, id: NodeId) = t.node(id).flatMap(_.statement.outside).collect {
    case OutsideFact.OnlyCodeChanges(m) => m
  }

  private def coded(t: Theory, c: Code): String = c match
    case Code.Proven(d)       => s"proven, ${t.vocabulary.define(d).fold(d.value)(_.written.source.value)}"
    case Code.ProvenFlow(f)   => s"proven program, ${t.vocabulary.define(f).fold(f.value)(_.written.source.value)}"
    case Code.Tested(runs, _) => s"Scala, ${runs.written.value}"
    case Code.Valued(v)       => s"the value ${Rows.shown(v)}"
    case Code.Provided        => "provided where the code runs"
    case Code.Modelled(m)     => s"meant by ${m.value}" +
      t.code.implemented.get(m).fold("")(i => s", its Scala tested against it: ${i.written.value}")

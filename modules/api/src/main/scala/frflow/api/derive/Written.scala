package frflow.api.derive

import frflow.api.view.source.*
import frflow.core.Theory
import frflow.core.analysis.resolution.Constrained
import frflow.core.code.Code
import frflow.core.expr.OutsideFact
import frflow.core.name.{DefName, NodeId}
import frflow.project.code.{Governance, Governed}
import frflow.project.pipeline.Analysis
import frflow.proof.lean.ast.ModuleName
import frflow.proof.lean.print.Print
import frflow.proof.layout.{Layout, NodePart}

/** What a node is written in (`Sources`), from the analysis: the sources and the proof files as read, the Lean as
  * `render` writes it.
  */
private[api] object Written:
  /** None when the model has no such node. */
  def of(a: Analysis, id: NodeId): Option[Sources] =
    val t = a.decided.theory
    t.node(id).map(_ => Sources(meanings(t, id), operations(t, id), files(a, id), generated(a, id), proof(a, id)))

  private def meanings(t: Theory, id: NodeId): List[Meaning] =
    Constrained.of(t, id).sortBy(_.value).flatMap(s => t.code.attached.get(s).map(c => Meaning(s, by(t, c.code))))

  /** What gives a Definition its meaning, with the text it is given by. */
  def by(t: Theory, c: Code): MeantBy = c match
    case Code.Proven(d)       => MeantBy.Proven(d, written(t, d))
    case Code.ProvenFlow(f)   => MeantBy.ProvenProgram(f, written(t, f))
    case Code.Tested(runs, _) => MeantBy.Tested(runs.written.value)
    case Code.Valued(v)       => MeantBy.Valued(v)
    case Code.Provided        => MeantBy.Provided
    case Code.Modelled(m)     => MeantBy.Modelled(m, t.code.implemented.get(m).map(_.written.value))

  private def written(t: Theory, d: DefName): String = t.vocabulary.define(d).fold(d.value)(_.written.source.value)

  /** Of the assumption that only the code changes a model's state: that model's operations' Scala. */
  private def operations(t: Theory, id: NodeId): List[Operations] =
    t.node(id).flatMap(_.statement.outside).toList.collect { case OutsideFact.OnlyCodeChanges(m) => m }
      .flatMap(m => t.code.implemented.get(m).map(i => Operations(m, i.written.value)))

  private def files(a: Analysis, id: NodeId): List[SourceFile] =
    Governance.of(a.decided.theory, a.inputs.sources.keys.toList, a.own).getOrElse(id, Nil).map {
      case Governed.Whole(p)        => SourceFile(p, FilePart.Whole, a.inputs.sources.get(p))
      case Governed.Named(p, names) => SourceFile(p, FilePart.Named(names), a.inputs.sources.get(p))
    }

  /** Its own modules in the order a reader takes them (what it states first), then its defines' modules. */
  private def generated(a: Analysis, id: NodeId): List[LeanText] =
    val t = a.decided.theory
    val l = Layout(t.name)
    val defines = Constrained.of(t, id).flatMap(t.code.attached.get).flatMap(_.code.proven).distinct.map(l.define)
    val names = NodePart.values.toList.map(l.ofNode(id, _)) ++ (l.refutes(id) :: defines)
    names.flatMap(n => a.modules.find(_.name == n).map(m => LeanText(n.dotted, n.file, Print.module(m))))

  private def proof(a: Analysis, id: NodeId): Option[LeanText] =
    val n: ModuleName = Layout(a.decided.theory.name).proofs(id)
    a.inputs.lean.proofs.get(id).map(f => LeanText(n.dotted, n.file, f.source))

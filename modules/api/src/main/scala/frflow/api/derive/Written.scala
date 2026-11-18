package frflow.api.derive

import frflow.api.view.source.*
import frflow.core.Theory
import frflow.core.analysis.resolution.Constrained
import frflow.core.code.Code
import frflow.core.name.{DefName, NodeId}
import frflow.project.code.{Governance, Governed}
import frflow.project.pipeline.Analysis
import frflow.proof.layout.{Layout, NodePart}
import frflow.proof.prover.ast.ModuleName
import frflow.proof.rocq.RocqProject

/** What a node is written in (`Sources`), from the analysis: the sources and the proof files as read, the Rocq as
  * `render` writes it.
  */
private[api] object Written:
  /** None when the model has no such node. */
  def of(a: Analysis, id: NodeId, rest: List[String]): Option[Sources] =
    val t = a.decided.theory
    t.node(id).map(_ => Sources(meanings(t, id), files(a, id), used(a, rest), generated(a, id), proof(a, id)))

  /** The proofs of the node's code and of every node below it, each by its module and its lemma: what
    * `Prover.uses` is asked of.
    */
  def proofs(a: Analysis, id: NodeId): List[(ModuleName, String)] =
    val (t, l) = (a.decided.theory, Layout(a.decided.theory.name))
    def below(n: NodeId): List[NodeId] = n :: t.refinement.parts(n).toList.flatMap(below)
    below(id).distinct.map(n => l.ofNode(n, NodePart.Impl) -> s"${n.value}_Impl_impl")
      .filter((m, _) => a.rocq.text(m).isDefined)

  /** The members of the model's classes among what the proofs rest on (`rest`), in their classes' files: a member's
    * define is named after its class and itself (`retiringLinks_remove`).
    */
  private def used(a: Analysis, rest: List[String]): List[SourceFile] =
    val defines = a.decided.theory.code.attached.values.flatMap(_.code.proven).map(_.value).toSet
    val members = rest.filter(defines).map(_.stripSuffix("_among").split("_", 2).toList).collect {
      case cls :: member :: Nil => cls.capitalize -> member }
    val files = a.inputs.sources.toList.sortBy(_._1.value)
    members.groupMap(_._1)(_._2).toList.sortBy(_._1).flatMap((cls, ms) =>
      files.find((_, text) => s"(class|object)\\s+$cls\\b".r.findFirstIn(text).isDefined)
        .map((path, text) => SourceFile(path, FilePart.Named(ms.distinct.sorted), Some(text))))

  private def meanings(t: Theory, id: NodeId): List[Meaning] =
    Constrained.of(t, id).sortBy(_.value).flatMap(s => t.code.attached.get(s).map(c => Meaning(s, by(t, c.code))))

  /** What gives a Definition its meaning, with the text it is given by. */
  def by(t: Theory, c: Code): MeantBy = c match
    case Code.Proven(d)       => MeantBy.Proven(d, written(t, d))
    case Code.Tested(runs, _) => MeantBy.Tested(runs.written.value)
    case Code.Valued(v)       => MeantBy.Valued(v)
    case Code.Provided        => MeantBy.Provided
    case Code.Executing(us)   => MeantBy.Executed(us.map(_.name))

  private def written(t: Theory, d: DefName): String = t.vocabulary.define(d).fold(d.value)(_.written.source.value)

  private def files(a: Analysis, id: NodeId): List[SourceFile] =
    Governance.of(a.decided.theory, a.inputs.sources.keys.toList, a.own).getOrElse(id, Nil).map {
      case Governed.Whole(p)        => SourceFile(p, FilePart.Whole, a.inputs.sources.get(p))
      case Governed.Named(p, names) => SourceFile(p, FilePart.Named(names), a.inputs.sources.get(p))
    }

  /** Its own modules in the order a reader takes them (what it states first), then its defines' modules. */
  private def generated(a: Analysis, id: NodeId): List[RocqText] =
    val t = a.decided.theory
    val l = Layout(t.name)
    val defines = Constrained.of(t, id).flatMap(t.code.attached.get).flatMap(_.code.proven).distinct.map(l.define)
    val names = NodePart.values.toList.map(l.ofNode(id, _)) ++ (l.refutes(id) :: defines)
    names.flatMap(n => a.rocq.text(n).map(text(n, _)))

  private def proof(a: Analysis, id: NodeId): Option[RocqText] =
    val n: ModuleName = Layout(a.decided.theory.name).proofs(id)
    a.inputs.proofs.files.get(id).map(f => text(n, f.source))

  private def text(n: ModuleName, source: String): RocqText =
    RocqText(RocqProject.logical(n), RocqProject.path(n), source)

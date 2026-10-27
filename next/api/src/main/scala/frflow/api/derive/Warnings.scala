package frflow.api.derive

import frflow.api.view.Warning
import frflow.core.name.{NodeId, RelPath}
import frflow.core.spec.Statement
import frflow.project.pipeline.Analysis
import frflow.proof.layout.Layout
import frflow.proof.obligation.{ObligationName, TryKind}
import frflow.proof.verdict.{ObligationStatus, Result}

/** What `status` warns of from the analysis: the decisions that do not count, files under two designs, source files
  * nothing governs, a design governing a path that is not there, proof files of no node, and nodes Lean proves
  * restate a part.
  */
private[api] object Warnings:
  def of(a: Analysis): List[Warning] =
    notCounted(a) ++ governedTwice(a) ++ ungoverned(a) ++ missing(a) ++ orphans(a) ++ restated(a)

  private def notCounted(a: Analysis): List[Warning] =
    a.inputs.ledger.others.map((id, d, why) => Warning.NotCounted(id, d, why))

  private def designs(a: Analysis): List[(NodeId, RelPath)] = a.decided.theory.nodes.map(_.node).flatMap(n =>
    n.statement match
      case Statement.Design(gs) => gs.toList.map(n.id -> _)
      case _                    => Nil)

  private def sources(a: Analysis): List[RelPath] = a.inputs.sources.keys.toList.sorted

  private def governedTwice(a: Analysis): List[Warning] = sources(a).flatMap { f =>
    val by = designs(a).collect { case (n, g) if f.isUnder(g) => n }.distinct
    Option.when(by.size > 1)(Warning.GovernedTwice(f, by))
  }

  /** A source file nothing governs, other than the model's own (where nodes and code are written, or the knowledge
    * base is put together).
    */
  private def ungoverned(a: Analysis): List[Warning] =
    val t = a.decided.theory
    val governed = a.governed.values.flatMap(_.files).toSet ++ designs(a).flatMap((_, g) =>
      sources(a).filter(_.isUnder(g))).map(_.value)
    val model = t.nodes.map(_.at.file).toSet ++ t.code.attached.values.map(_.writtenIn)
    a.inputs.sources.toList.sortBy(_._1).collect {
      case (f, text) if !governed(f.value) && !model(f) && !text.contains("KnowledgeBase(") => Warning.Ungoverned(f)
    }

  private def missing(a: Analysis): List[Warning] = designs(a).collect {
    case (n, g) if !sources(a).exists(_.isUnder(g)) => Warning.GovernedMissing(g, n)
  }

  private def orphans(a: Analysis): List[Warning] =
    val layout = Layout(a.decided.theory.name)
    a.inputs.proofs.keys.toList.sortBy(_.value)
      .filter(id => id.value != "Lemmas" && a.decided.theory.node(id).isEmpty)
      .map(id => Warning.ProofFileOfNoNode(layout.proofs(id).file))

  /** A node Lean proves equivalent to its one part (`restates` shown, `complete` proven), or a part it proves
    * equivalent to a conjunct (`restates_<i>` shown).
    */
  private def restated(a: Analysis): List[Warning] = a.decided.theory.nodes.map(_.node.id).flatMap { id =>
    val rs = a.current(id).toList.flatMap(_.results)
    def shown(r: Result) = r.status == ObligationStatus.Shown
    val complete = rs.exists(r => r.name == ObligationName.Complete && r.status == ObligationStatus.Proven)
    rs.filter(shown).flatMap(_.name match
      case ObligationName.Tried(TryKind.Restates) if complete =>
        a.decided.theory.refinement.parts(id).map(Warning.Restates(id, _))
      case ObligationName.Tried(TryKind.RestatesConjunct(p, _)) => List(Warning.Restates(id, p))
      case _                                                   => Nil)
  }

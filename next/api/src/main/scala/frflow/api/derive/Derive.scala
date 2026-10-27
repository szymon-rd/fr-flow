package frflow.api.derive

import frflow.api.view.{View, Views, Warning}
import frflow.core.checking.Checking
import frflow.project.pipeline.Analysis

/** The view derived once from the analysis: each node's view in decision order, the roots, the theory as a whole,
  * the overview, the warnings (the shell's, given, then the analysis's), and the decided nodes gone from the model.
  */
private[api] object Derive:
  def of(a: Analysis, shell: List[Warning]): View =
    val views = NodeViews(a)
    val nodes = a.subjects.inOrder.flatMap(s => a.decided.theory.node(s.id)).map(views.of)
    val whole = Wholes.of(a)
    val gone = a.reading.gone
    View(nodes, a.decided.theory.refinement.roots.map(_.id), whole, Views.overview(nodes, whole, gone),
      shell ++ Warnings.of(a) ++ Wholes.warnings(whole) ++ unchecked(a), gone)

  /** `status` says it of each claim nothing checks (`Checking.unchecked`): its parts do not prove it, and the plain
    * Scala it is about cannot be tested against it.
    */
  def unchecked(a: Analysis): List[Warning] =
    a.decided.theory.nodes.map(_.node.id).filter(Checking.unchecked(a.decided.theory, _)).map(Warning.NotChecked(_))

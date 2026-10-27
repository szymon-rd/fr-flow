package frflow.core.analysis

import frflow.core.{Kb, Lang, Store}
import frflow.core.Nodes.*
import frflow.core.expr.OutsideFact
import frflow.core.name.NodeId

/** One theory per problem of the graph: its shape, and what may be a premise or a part. */
object GraphCases:
  private def id(s: String) = NodeId(s)
  private val root = plain("root")
  private val fact = outside("fact")(OutsideFact.OneRunAtATime(Store.model))
  private val saysFact = Lang.formula([T[_]] => (l: Lang[T]) => l.s.outside(OutsideFact.OneRunAtATime(Store.model)))

  val all: List[ProblemCase] = List(
    ProblemCase(Kb.of(plain("a"), plain("a")), List(Problem.DuplicateId(id("a")))),
    ProblemCase(Kb.of(assumption("trusted")(Lang.truth)), List(Problem.NoRoot)),
    ProblemCase(Kb.of(root, plain("a"), plain("b")).linking(partOf("a", "b"), partOf("b", "a")),
      List(Problem.AboveItself(id("a")), Problem.AboveItself(id("b")))),
    ProblemCase(Kb.of(root, plain("a")).linking(partOf("a", "gone")), List(Problem.ParentOutside(id("a"), id("gone")))),
    ProblemCase(Kb.of(root, design("layout")), List(Problem.DesignWithoutParent(id("layout")))),
    ProblemCase(Kb.of(root, design("layout"), plain("below")).linking(partOf("layout", "root"),
      partOf("below", "layout")), List(Problem.UnderDesign(id("below"), id("layout")))),
    ProblemCase(Kb.of(root, plain("other")).linking(assumes("root", "other")),
      List(Problem.PremiseNotAssumed(id("root"), id("other")))),
    ProblemCase(Kb.of(root, assumption("premise")(Lang.truth)).linking(assumes("root", "premise"),
      partOf("premise", "root")), List(Problem.PremiseBelow(id("root"), id("premise")))),
    ProblemCase(Kb.of(root, fact).linking(partOf("fact", "root")), List(Problem.OutsideAsPart(id("fact"), id("root")))),
    ProblemCase(Kb.of(root, claim("claimedFact")(saysFact)),
      List(Problem.OutsideClaimed(id("claimedFact")))))

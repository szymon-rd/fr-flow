package frflow.core.analysis

import frflow.core.Store
import frflow.core.Nodes.*
import frflow.core.expr.OutsideFact
import frflow.core.name.NodeId

/** One theory per problem of the world outside, each the store's valid theory with one change. */
object OutsideCases:
  private def id(s: String) = NodeId(s)

  /** The claim about `book`'s runs no longer lists that runs come one at a time; the assumption saying it is there. */
  val missing: ProblemCase = ProblemCase(Store.kb.unlinking(assumes("bookRuns", "oneAtATime")),
    List(Problem.PremiseMissing(id("bookRuns"), Premise.OneRunAtATime(Store.model), Some(id("oneAtATime")))))

  val all: List[ProblemCase] = List(
    missing,
    ProblemCase(Store.kb.and(plain("unrelated")).linking(assumes("unrelated", "oneAtATime")),
      List(Problem.PremiseNotNeeded(id("unrelated"), id("oneAtATime")))),
    ProblemCase(Store.kb.and(outside("nobodyWrites")(OutsideFact.WrittenOnlyBy(Store.model, Nil))),
      List(Problem.WriterNotListed(Store.model, Store.book))))

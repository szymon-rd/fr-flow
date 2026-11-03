package frflow.project

import frflow.core.analysis.{Callees, Resolve}
import frflow.core.analysis.outside.Reads
import frflow.core.name.{NodeId, SymbolName}
import frflow.eval.flow.Stamps

/** A `cover_` built as `impl` is (2.7) takes what is said of what the program calls but has no proven code, and never
  * a claim resting on the rule it covers (`Reads.restsOn`): the picking's claim, read where every stamp is not
  * negative, is no hypothesis of that rule's `cover_picking`, so the rule is not kept by being assumed.
  */
class CoverCircleSuite extends munit.FunSuite:
  private val elaborated = Projects.elaborated(Stamps.circling)
  private val t = Projects.bare(elaborated).decided.theory
  private val (rule, claim) = (NodeId("nonNegative"), NodeId("pickedNonNegative"))

  test("a claim about a callee that rests on the rule is said of the callee, and is no hypothesis of its cover_") {
    assert(Resolve.constrainingCalled(t, Some(Callees.within(t, SymbolName("picking")))).contains(claim))
    assert(Reads.restsOn(t, claim, rule))
    val spec = Projects.bare(elaborated).modules.find(_.name.dotted == "FrFlowGen.Picking.nonNegative.Spec")
      .map(frflow.proof.lean.print.Print.module).getOrElse(fail("no nonNegative spec"))
    val cover = spec.linesIterator.dropWhile(!_.contains("def cover_picking")).take(2).mkString("\n")
    assert(cover.contains("cover_picking") && !cover.contains("pickedNonNegative"), cover)
  }

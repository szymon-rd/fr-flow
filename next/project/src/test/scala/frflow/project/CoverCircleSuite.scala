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
  /** The rule's `cover_picking`, as its Spec states it. */
  private lazy val cover: String =
    val spec = Projects.bare(elaborated).modules.find(_.name.dotted == "FrFlowGen.Picking.nonNegative.Spec")
      .map(frflow.proof.lean.print.Print.module).getOrElse(fail("no nonNegative spec"))
    spec.linesIterator.dropWhile(!_.contains("def cover_picking")).take(2).mkString("\n")

  test("a claim about a callee that rests on the rule is said of the callee, and is no hypothesis of its cover_") {
    assert(Resolve.constrainingCalled(t, Some(Callees.within(t, SymbolName("picking")))).contains(claim))
    assert(Reads.restsOn(t, claim, rule))
    assert(cover.contains("cover_picking") && !cover.contains("pickedNonNegative"), cover)
  }

  test("a claim proven from a claim taking the rule rests on the rule too: it is no hypothesis of the cover_") {
    val always = NodeId("pickedAlways")
    assert(Resolve.constrainingCalled(t, Some(Callees.within(t, SymbolName("picking")))).contains(always))
    assert(!Reads.takes(t, always, rule) && Reads.restsOn(t, always, rule))
    assert(!cover.contains("pickedAlways"), cover)
  }

  test("an assumption about the covered program itself is no hypothesis of its cover_ (the 13d review's S2)") {
    val keeps = NodeId("pickingKeeps")
    assert(Resolve.constrainingCalled(t, Some(Callees.within(t, SymbolName("picking")))).contains(keeps))
    assert(!cover.contains("pickingKeeps"), cover)
  }

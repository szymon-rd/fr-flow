package frflow.core.analysis

import frflow.core.analysis.resolution.Resolve
import frflow.core.name.NodeId

/** What a claim checked against code relies on, a claim about other code that would close a circle left out
  * (`Relying`); a circle of claims about what the code calls still rests on itself.
  */
class RelyingSuite extends munit.FunSuite:
  test("a claim about other code that would close a circle is left out of what a claim's code relies on, the first " +
    "kept: two claims on code calling one word rest on no circle") {
    val kb = ValueCases.sharedWord
    assertEquals(Resolve.reliesOn(kb.theory, NodeId("aboutG")), List(NodeId("aboutF")))
    assertEquals(Resolve.reliesOn(kb.theory, NodeId("aboutF")), List(NodeId("aboutG")))
    assertEquals(kb.problems, Nil)
    val r = Resolve(Validate(kb.elaborated).toOption.get)
    assertEquals(List("aboutF", "aboutG").map(n => r.reliesOn(NodeId(n))), List(List(NodeId("aboutG")), Nil))
    assertEquals(Resolve.circles(ValueCases.mutual.theory), List(List(NodeId("aboutF"), NodeId("aboutG"))))
  }

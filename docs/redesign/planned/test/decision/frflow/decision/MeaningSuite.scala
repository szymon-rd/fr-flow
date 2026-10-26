package frflow.decision

import frflow.decision.content.{Content, FieldValue}
import frflow.decision.review.Meaning

/** Moving a node under another parent: a design's own meaning moves (placing it is decided), a claim's does not. */
class MeaningSuite extends munit.FunSuite:
  private def node(kind: String, parent: String) = Content(List("kind" -> FieldValue.Text(kind),
    "parents" -> FieldValue.Texts(List(parent)), "statement" -> FieldValue.Text("It holds.")))

  test("a design moved under another contract is under review for itself") {
    assertNotEquals(Meaning.own(node("design", "A")).hash, Meaning.own(node("design", "B")).hash)
  }

  test("a claim moved under another whole is not: its chain says so") {
    assertEquals(Meaning.own(node("claim", "A")).hash, Meaning.own(node("claim", "B")).hash)
  }

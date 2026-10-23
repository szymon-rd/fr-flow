package frflow.cli

import cats.effect.IO
import frflow.api.*
import frflow.protocol.*

/** The views in plain mode, against golden files: what an agent or CI reads. */
class ViewsSuite extends munit.CatsEffectSuite with Golden:
  private val st = Style(color = false, unicode = false, width = Some(100))
  private def api = FakeApi()

  test("tree: the DAG from the root, the sections, the summary") {
    api.flatMap(_.tree(None)).map(t => golden("tree", TreeText.lines(t, st)))
  }

  test("tree --all: statements in full, wrapped under the node") {
    api.flatMap(_.tree(None)).map(t => golden("tree-all", TreeText.lines(t, st.copy(width = Some(72)), full = true)))
  }

  test("show: a node under review, with what changed and what deciding it acts on") {
    api.flatMap(_.details(NodeId("Decide"))).map(d => golden("show-review", NodeText.lines(d, st)))
  }

  test("show: a proposal waiting for its parent") {
    api.flatMap(_.details(NodeId("Expiry"))).map(d => golden("show-proposed", NodeText.lines(d, st)))
  }

  test("inbox: requests, the developer's queue, the agent's tasks, then the tree") {
    api.flatMap(_.view).map(v => golden("inbox", InboxText.lines(Inbox.of(v), Trees.of(v, None).toOption.get, st)))
  }

  test("colors are ANSI codes around the same text") {
    api.flatMap(_.tree(None)).map { t =>
      val colored = TreeText.lines(t, st.copy(color = true))
      assert(colored.exists(_.contains("\u001b[32m")))
      assertEquals(colored.map(Style.strip), TreeText.lines(t, st))
    }
  }

  test("a statement is cut to the width, with an ellipsis") {
    assertEquals(st.cut("a user gets access", 10), "a user...")
    assertEquals(Style(true, true, None).cut("a user gets access", 10), "a user ge…")
    assertEquals(st.wrap("one two three four", 9), List("one two", "three", "four"))
  }

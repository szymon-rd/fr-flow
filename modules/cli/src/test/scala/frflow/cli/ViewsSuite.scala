package frflow.cli

import frflow.api.*
import frflow.protocol.*

/** The views in plain mode, against golden files: what an agent or CI reads. */
class ViewsSuite extends munit.CatsEffectSuite with Golden:
  private val st = Style(color = false, unicode = false, width = Some(100))
  private def api = FakeApi()

  test("tree: the DAG from the root, the sections, the summary; from a node, what is below it") {
    api.flatMap(_.tree(None)).map(t => golden("tree", TreeText.lines(t, st))) *>
      api.flatMap(_.tree(Some(NodeId("LetsIn")))).map(t => golden("tree-node", TreeText.lines(t, st)))
  }

  test("show: a node under review, with what changed and what deciding it acts on; a proposal waiting for its parent") {
    api.flatMap(_.details(NodeId("Decide"))).map(d => golden("show-review", NodeText.lines(d, st))) *>
      api.flatMap(_.details(NodeId("Expiry"))).map(d => golden("show-proposed", NodeText.lines(d, st)))
  }

  test("diff: a proposal is new; a change is shown once, field by field") {
    for
      expiry <- api.flatMap(_.diff(NodeId("Expiry")))
      decide <- api.flatMap(_.diff(NodeId("Decide")))
    yield
      assertEquals(DiffText.lines(expiry, st).headOption, Some("New: never decided"))
      assertEquals(decide.self.map(_.field), List("statement"))
  }

  test("context (show --full): with the idea, what it rests on and the obligations; nothing cut") {
    api.flatMap(_.details(NodeId("Decide"))).map(d => golden("context", NodeText.lines(d, st, Depth.Full)))
  }

  test("--json: the typed value, each node in brief") {
    api.flatMap(_.tree(None)).map { t =>
      val j = Brief(io.circe.syntax.EncoderOps(t).asJson)
      val root = j.hcursor.downField("main").downArray.downField("node")
      assertEquals(root.keys.map(_.toList), Some(List("id", "kind", "state", "causes", "status", "statement", "waitsFor", "unproven")))
    }
  }

  test("inbox: requests, the developer's queue, the agent's tasks, then the summary") {
    api.flatMap(_.view).map(v => golden("inbox", InboxText.lines(Inbox.of(v), st)))
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
    assertEquals(Style(true, true, None).cut("a user gets access", 10), "a user ge…\u001b[0m")
    assertEquals(Style.strip(Style(true, true, None).cut(Style(true, true, None).green("a user gets access"), 10)), "a user ge…")
    assertEquals(st.wrap("one two three four", 9), List("one two", "three", "four"))
  }

  test("a source or diff line is wrapped under its text, its colors kept; nothing is cut") {
    val narrow = Style(color = false, unicode = false, width = Some(24))
    assertEquals(narrow.fold("  - one two three four five six"), List("  - one two three four", "    five six"))
    val colored = narrow.copy(color = true).fold("  " + narrow.copy(color = true).red("- one two three four five six"))
    assertEquals((colored.map(Style.strip), colored(1).take(9)), (narrow.fold("  - one two three four five six"), "    \u001b[31m"))
  }

  test("colors and Unicode only on a terminal, without --plain or NO_COLOR; lines cut only on a terminal") {
    val env = Map("COLUMNS" -> "80")
    assertEquals(List(Style.of(false, env, terminal = true), Style.of(true, env, terminal = true), Style.of(false, env + ("NO_COLOR" -> "1"), terminal = true),
      Style.of(false, env, terminal = false)), List(Style(true, true, Some(80)), Style(false, false, Some(80)), Style(false, false, Some(80)), Style(false, false, None)))
  }

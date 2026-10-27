package frflow.cli

import cats.effect.IO
import cats.syntax.all.*
import frflow.api.{Opened, Project}
import frflow.cli.command.Command
import frflow.cli.term.{Style, Terminal}
import frflow.cli.text.Depth
import frflow.core.name.NodeId

/** What the reading commands print, and how lines meet a terminal: colors, Unicode, the width. */
class ViewsSuite extends munit.CatsEffectSuite:
  private val (nonNegative, sameAbove) = (NodeId("nonNegative"), NodeId("sameAbove"))
  private val color = Style(color = true, unicode = true, width = None)

  private def shown(p: Project[IO], cs: Command*) = Opened.api(p).flatMap(Cli.all(_, cs*)).map(_._2)
  private def moved(p: Project[IO], cs: Command*) = Opened.ports().flatMap(ports =>
    Opened.over(Opened.before, ports).flatMap(Cli.accepted) >> Opened.over(p, ports)).flatMap(Cli.all(_, cs*))
    .map(_._2)

  test("tree: the DAG from the roots, the summary; from a node, what is below it") {
    (shown(Opened.before, Command.Tree(None)), shown(Opened.before, Command.Tree(Some(sameAbove)))).tupled.map {
      (all, below) =>
        assert(all.startsWith("! nonNegative  claim  proposed  The service never gives a negative number.\n" +
          "  ! sameAbove  claim  proposed  Above zero, the service gives the number itself."), all)
        assert(all.contains("FrModel: 2 nodes, 0 accepted, 2 proposed"), all)
        assert(all.contains("Waiting: 2 for the developer"), all)
        assert(below.startsWith("! sameAbove"), below)
    }
  }

  test("show: a node under review, with what moved and what deciding it acts on; a proposal waiting for its parent") {
    (moved(Opened.after, Command.Show(nonNegative, Depth.Normal), Command.Show(sameAbove, Depth.Normal)),
      shown(Opened.before, Command.Show(sameAbove, Depth.Normal))).tupled.map { (review, proposal) =>
      assert(review.contains("to review: it changed"), review)
      assert(review.contains("decisions below it that accepting it acts on (accept --revisit NODE reviews one " +
        "again): sameAbove"), review)
      assert(review.contains("moved above it since it was decided: nonNegative (diff sameAbove shows how)"), review)
      assert(proposal.contains("decide nonNegative first: what rests on it is decided after it"), proposal)
      assert(proposal.contains("Formally (as written in Scala)"), proposal)
    }
  }

  test("a node not decided shows no why section; one decided shows the reason it was decided with") {
    (shown(Opened.before, Command.Show(nonNegative, Depth.Normal)),
      moved(Opened.before, Command.Show(nonNegative, Depth.Normal))).tupled.map { (proposal, accepted) =>
      assert(!proposal.contains("Why it holds"), proposal)
      assert(accepted.contains("Why it holds (the reason it was decided with)\n  it says what the service must do " +
        " (accepted by ann, "), accepted)
    }
  }

  test("diff: a proposal is new; what moved under a decision is its fields, line by line") {
    (shown(Opened.before, Command.Diff(nonNegative)), moved(Opened.after, Command.Diff(nonNegative))).tupled.map {
      (fresh, moved) =>
        assertEquals(fresh, "nonNegative is not decided yet: everything in it is new (show nonNegative reads it)")
        assert(moved.contains("formula:\n- "), moved)
        assert(moved.linesIterator.exists(_.startsWith("+ ")), moved)
    }
  }

  test("show --full: what it mentions and every obligation; nothing cut") {
    Opened.api(Opened.before).flatMap(api => Opened.checked(api.proving.check(None)) >>
      Scripted(Nil, interactive = false).flatMap(t => Cli.run(api, t, Command.Show(nonNegative, Depth.Full),
        Style.plain.copy(width = Some(30))) >> t.text)).map { full =>
      assert(full.contains("What it mentions\n  values: d"), full)
      assert(full.contains("check: proven"), full)
      assert(full.contains("The service never gives a negative number."), full)
    }
  }

  test("--json: status prints the snapshot, as export writes it") {
    shown(Opened.before, Command.Status(json = true), Command.Export).map { out =>
      assert(out.startsWith("{\n  \"version\": "), out)
      assertEquals(out.linesIterator.count(_ == "{"), 2, out)
    }
  }

  test("inbox: the developer's queue in order, then the summary") {
    shown(Opened.before, Command.Inbox).map { out =>
      assert(out.startsWith("To decide, in order (review, or accept / reject NODE)\n  ! nonNegative"), out)
      assert(out.contains("  ! sameAbove  claim  proposed  Above zero, the service gives the number itself.\n" +
        "    decide nonNegative first"), out)
    }
  }

  test("colors are ANSI codes around the same text") {
    assertEquals(color.red("x"), "\u001b[31mx\u001b[0m")
    assertEquals(Style.strip(color.bold(color.green("ok"))), "ok")
    assertEquals(Style.plain.red("x"), "x")
  }

  test("a statement is cut to the width, with an ellipsis") {
    val st = Style.plain.copy(width = Some(30))
    assertEquals(st.fit("a statement longer than thirty columns"), "a statement longer than thi...")
    assertEquals(Style.visible(color.copy(width = Some(30)).fit(color.bold("a statement longer than thirty columns"))),
      30)
  }

  test("a node's statement is wrapped under its header in show: nothing is cut") {
    Opened.api(Opened.before).flatMap(api => Scripted(Nil).flatMap(t =>
      Cli.run(api, t, Command.Show(sameAbove, Depth.Normal), Style.plain.copy(width = Some(30))) >> t.output)).map {
      out =>
        val statement = out.slice(1, out.indexOf(""))
        assert(statement.size > 1 && out.forall(Style.visible(_) <= 30), out)
        assertEquals(statement.map(_.trim).mkString(" "), "Above zero, the service gives the number itself.")
    }
  }

  test("a source or diff line is wrapped under its text, its colors kept; nothing is cut") {
    val st = color.copy(width = Some(24))
    val folded = st.fold("  " + st.green("+ forall n, d(n) >= 0 and d(n) is the number"))
    assert(folded.size > 1 && folded.forall(Style.visible(_) <= 24), folded)
    assertEquals(folded.map(Style.strip).mkString(" ").replaceAll("\\s+", " ").trim,
      "+ forall n, d(n) >= 0 and d(n) is the number")
  }

  test("colors and Unicode only on a terminal, without --plain or NO_COLOR; lines cut only on a terminal") {
    val env = Map("COLUMNS" -> "80")
    assertEquals(Style.of(plain = false, env, terminal = true), Style(true, true, Some(80)))
    assertEquals(Style.of(plain = true, env, terminal = true), Style(false, false, Some(80)))
    assertEquals(Style.of(plain = false, env + ("NO_COLOR" -> "1"), terminal = true), Style(false, false, Some(80)))
    assertEquals(Style.of(plain = false, env, terminal = false), Style(false, false, None))
  }

  test("a terminal is the console's own answer where the JDK has one (22 and later), else a console being there") {
    assert(Terminal.attached[Int](Some(1), _ => None))
    assert(!Terminal.attached[Int](Some(1), _ => Some(false)))
    assert(!Terminal.attached[Int](None, _ => Some(true)))
  }

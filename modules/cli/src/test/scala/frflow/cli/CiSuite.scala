package frflow.cli

import cats.effect.{ExitCode, IO}
import com.monovore.decline.Command as Sub
import frflow.api.view.View
import frflow.api.{FrFlowApi, Host, Lean, Opened}
import frflow.cli.command.{CliExtension, Command, Dispatch}
import frflow.cli.review.ReviewKey
import frflow.cli.term.{Style, Terminal}
import frflow.cli.text.Contribution
import frflow.core.name.RelPath
import frflow.decision.ledger.Ledger
import frflow.project.Projects
import frflow.project.port.Records
import frflow.wire.file.Files as Wire
import frflow.wire.ledger.LedgerFile

/** `ci` exits 0 only when the FrModel is complete and nothing is warned, FrFlow's or a layer's; `rebase` lists what it
  * accepts before it asks, and refuses when there is nothing to accept; what reaches a terminal has no control
  * characters but the colors.
  */
class CiSuite extends munit.CatsEffectSuite:
  /** A layer on top that warns of one thing. */
  private object Warns extends CliExtension:
    def commands: List[Sub[(Command, Boolean)]] = Nil
    def contribute(host: Host[IO], v: View, st: Style): IO[Contribution] =
      IO.pure(Contribution.empty.copy(warnings = List("a layer warns")))
    def keys(host: Host[IO]): List[ReviewKey] = Nil

  /** Every node accepted where its proof fails. */
  private def failing: IO[FrFlowApi[IO]] =
    Opened.api(Opened.trusted, lean = Lean.Proving(Set("complete"), Set.empty)).flatMap(Cli.accepted)

  test("ci exits 1 for a complete project that warns, for a layer's warning, for an empty model, a failing check") {
    val other = RelPath.fromIdentifiers("src/main", "Other.scala")
    for
      ports     <- Opened.ports(Map(other -> "object Other"))
      warned    <- Opened.over(Opened.trusted, ports).flatMap(Cli.accepted)
      complete  <- warned.reading.view.map(_.overview.complete)
      (w, text) <- Cli.all(warned, Command.Ci)
      fine      <- Opened.api(Opened.trusted).flatMap(Cli.accepted)
      term      <- Scripted(Nil, interactive = false)
      layer     <- Dispatch(fine, Cli.host(fine), term, Cli.plain)(List(Warns))(Command.Ci)
      alone     <- Cli.all(fine, Command.Ci).map(_._1)
      (e, _)    <- Opened.api(Opened.project(Shelves.Empty.kb)).flatMap(Cli.all(_, Command.Ci))
      (f, ft)   <- failing.flatMap(Cli.all(_, Command.Ci))
    yield
      assert(complete, "the FrModel itself is complete")
      assert(text.contains("warning: no node governs src/main/Other.scala"), text)
      assert(ft.contains("o aboveMinusOne: open"), ft)
      assertEquals(w ++ List(layer) ++ alone ++ e ++ f, List(1, 1, 0, 1, 1).map(ExitCode(_)))
  }

  test("rebase lists what it accepts before it records anything, and refuses when nothing was rewritten") {
    val ledger = Records.path(LedgerFile.format)
    for
      p          <- Projects.inMemory(Map.empty)
      api        <- Opened.over(Opened.before, p.ports)
      _          <- Cli.accepted(api)
      _          <- p.ports.ledger.load.flatMap(l => p.git.commit(Map(ledger -> Wire.print(LedgerFile.format, l))))
      (none, n)  <- Cli.all(api, Command.Rebase(Some("ann"), yes = true))
      _          <- p.ports.ledger.update(_ => Right((Ledger.empty, ())))
      (done, t)  <- Cli.all(api, Command.Rebase(Some("ann"), yes = true))
    yield
      assertEquals(none ++ done, List(ExitCode(1), ExitCode(0)))
      assert(n.contains("there is nothing to rebase"), n)
      assert(t.contains("Rebasing accepts the ledger as it reads now, which no longer holds what was committed:\n" +
        "  - accepted nonNegative by ann (it says what the service must do): what was committed"), t)
      assert(t.contains("wrote .frflow/ledger-base"), t)
  }

  test("what reaches a terminal has no control characters, but new lines, tabs and the colors Style adds") {
    val st = Style(color = true, unicode = true, width = None)
    assertEquals(Terminal.clean(st.red("a") + "\u001b[2J\u001b[1;1Hb\u0007\u009bc\n\td"),
      st.red("a") + "[2J[1;1Hbc\n\td")
  }

package frflow.cli

import cats.effect.{ExitCode, IO}
import frflow.api.{FrFlowApi, Host, Opened}
import frflow.cli.command.{Command, Dispatch}
import frflow.cli.term.Style
import java.nio.file.Path

/** Commands run as the command line runs them, over the API in memory, a terminal scripted. */
object Cli:
  val plain: Style = Style.plain

  def host(api: FrFlowApi[IO]): Host[IO] = Host(api, Path.of(".").toAbsolutePath.normalize, Map.empty)

  /** What stops it said, with its exit code, as `Launch` does. */
  def run(api: FrFlowApi[IO], term: Scripted, c: Command, st: Style = plain): IO[ExitCode] =
    Dispatch(host(api), term, st, Nil)(c).handleErrorWith(Launch.failed(term, _))

  /** Each command on a fresh terminal not on a terminal: the exit codes, and all that was written. */
  def all(api: FrFlowApi[IO], cs: Command*): IO[(List[ExitCode], String)] =
    Scripted(Nil, interactive = false).flatMap(t =>
      cs.toList.foldLeft(IO.pure(List.empty[ExitCode]))((acc, c) =>
        acc.flatMap(codes => run(api, t, c).map(codes :+ _)))
        .flatMap(codes => t.text.map(codes -> _)))

  /** Every node checked and accepted, as `ann`. */
  def accepted(api: FrFlowApi[IO]): IO[FrFlowApi[IO]] = Opened.acceptAll(api).as(api)

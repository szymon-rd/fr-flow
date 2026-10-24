package frflow.web

import cats.effect.{ExitCode, IO, IOApp}
import cats.effect.std.Console
import frflow.api.FrFlowProject

/** The web view of a project, run by its sbt task: `sbt "auth/serve --port 8765 --as NAME"`. The task passes the
  * project's main object (`auth.authCli`, a `FrFlowProject`) first; the rest are the task's arguments.
  */
object Serve extends IOApp:
  private val Usage = "usage: sbt \"PROJECT/serve [--port N] [--as NAME]\"  (port 8765 by default; 0 for any free one)"

  def run(args: List[String]): IO[ExitCode] = args match
    case main :: rest => options(rest, 8765, None) match
      case Right((port, as)) =>
        for
          project <- project(main)
          env <- IO(sys.env)
          host <- project.host(env)
          dev <- host.api.developer(as)
          layers = project.extensions.collect { case w: WebExtension => w }
          code <- dev.fold(r => Console[IO].errorln(r.message).as(ExitCode(2)), WebView.serve(host, _, port, layers).as(ExitCode.Success))
        yield code
      case Left(why) => Console[IO].errorln(s"$why\n$Usage").as(ExitCode(2))
    case Nil => Console[IO].errorln(Usage).as(ExitCode(2))

  private def options(args: List[String], port: Int, as: Option[String]): Either[String, (Int, Option[String])] = args match
    case Nil => Right((port, as))
    case "--port" :: p :: rest => p.toIntOption.filter(n => n >= 0 && n < 65536).toRight(s"not a port: $p").flatMap(options(rest, _, as))
    case "--as" :: name :: rest => options(rest, port, Some(name))
    case other :: _ => Left(s"unknown argument: $other")

  /** The project's main object, by its class name. */
  private def project(main: String): IO[FrFlowProject] = IO {
    Class.forName(main.stripSuffix("$") + "$").getField("MODULE$").get(null) match
      case p: FrFlowProject => p
      case _ => throw IllegalArgumentException(s"$main is not a FrFlow project's main object (a FrFlowApp)")
  }

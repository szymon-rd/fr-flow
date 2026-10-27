package frflow.web

import cats.effect.std.Console
import cats.effect.{ExitCode, IO, IOApp}
import cats.syntax.all.*
import frflow.api.{FrFlowApi, FrFlowProject, Host}

/** The web view of a project, run by its sbt task: `sbt "rooms/serve --port 8765 --as NAME"`. The task passes the
  * project's main object (`rooms.roomsCli`, a `FrFlowProject`) first; the rest are the task's arguments. Who decides
  * is `--as`, else `FRFLOW_AS`, else the name the developer's key is listed under.
  */
object Serve extends IOApp:
  private val Usage = "usage: sbt \"PROJECT/serve [--port N] [--as NAME]\"  (port 8765 by default; 0 for any free one)"

  def run(args: List[String]): IO[ExitCode] = args match
    case main :: rest => options(rest, 8765, None).fold(why => Console[IO].errorln(s"$why\n$Usage").as(ExitCode(2)),
        (port, as) => project(main).flatMap(served(_, port, as)))
    case Nil          => Console[IO].errorln(Usage).as(ExitCode(2))

  private def served(p: FrFlowProject, port: Int, as: Option[String]): IO[ExitCode] =
    IO(sys.env).flatMap(env => p.project.flatMap(_.fold(
      es => es.traverse_(e => Console[IO].errorln(s"error: $e")).as(ExitCode(1)),
      project => FrFlowApi.make[IO](project, p.directory(env), env).use { api =>
        val host = Host.of(api, p.directory(env), env)
        val layers = p.extensions.collect { case w: WebExtension => w }
        api.deciding.developer(as).flatMap(_.fold(r => Console[IO].errorln(s"who decides? $r: pass --as NAME")
          .as(ExitCode(2)), WebView.serve(api, host, _, port)(layers).as(ExitCode.Success)))
      })))

  private def options(args: List[String], port: Int, as: Option[String]): Either[String, (Int, Option[String])] =
    args match
      case Nil                    => Right((port, as))
      case "--port" :: p :: rest  =>
        p.toIntOption.filter(n => n >= 0 && n < 65536).toRight(s"not a port: $p").flatMap(options(rest, _, as))
      case "--as" :: name :: rest => options(rest, port, Some(name))
      case other :: _             => Left(s"unknown argument: $other")

  /** The project's main object, by its class name. */
  private def project(main: String): IO[FrFlowProject] = IO(
    Class.forName(main.stripSuffix("$") + "$").getField("MODULE$").get(null)).flatMap {
    case p: FrFlowProject => IO.pure(p)
    case _                => IO.raiseError(IllegalArgumentException(s"$main is not a FrFlow project's main object"))
  }

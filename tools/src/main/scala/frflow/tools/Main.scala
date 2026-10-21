package frflow.tools

import java.io.PrintStream
import java.nio.charset.StandardCharsets.UTF_8

/** `frflow serve [--host H] [--port N] PATH...` starts the browser;
  * `frflow mcp PATH...` serves MCP on stdin/stdout.
  * A PATH is a project (a directory with `frflow.json`) or a directory of projects.
  */
object Main:
  val usage = "usage: frflow serve [--host 127.0.0.1] [--port 8765] PATH... | frflow mcp PATH..."

  def main(args: Array[String]): Unit = args.toList match
    case "serve" :: rest =>
      def opt(name: String) = rest.sliding(2).collectFirst { case List(`name`, v) => v }
      val paths = rest.foldLeft((List.empty[String], false)) { case ((acc, skip), a) =>
        if skip then (acc, false) else if a.startsWith("--") then (acc, true) else (acc :+ a, false)
      }._1
      val projects = Project.find(if paths.isEmpty then List(".") else paths)
      if projects.isEmpty then { System.err.println("no project found (a project is a directory with frflow.json)"); sys.exit(2) }
      val host = opt("--host").getOrElse("127.0.0.1")
      val server = Server(projects).serve(host, opt("--port").map(_.toInt).getOrElse(8765))
      println(s"FrFlow browser on http://$host:${server.getAddress.getPort}  (${projects.map(_.name).mkString(", ")})")
      Thread.currentThread.join()
    case "mcp" :: paths =>
      // stdout carries the protocol; everything else goes to stderr.
      val protocol = PrintStream(java.io.FileOutputStream(java.io.FileDescriptor.out), true, UTF_8)
      System.setOut(System.err)
      Mcp(Project.find(if paths.isEmpty then List(".") else paths)).serve(System.in, protocol)
    case _ => System.err.println(usage); sys.exit(2)

package frflow.tools

import frflow.Json
import frflow.Json.*
import java.io.{BufferedReader, InputStreamReader, PrintStream}
import java.nio.charset.StandardCharsets.UTF_8

/** The FrFlow MCP server (stdio): how an agent works on a knowledge base.
  *
  * Tools run the knowledge base's CLI, which builds everything from the Scala
  * definitions. The agent proposes nodes and answers the developer's requests;
  * deciding is the developer's, in the browser, so there is no tool to accept a node.
  */
final class Mcp(projects: List[Project]):
  private val byName = projects.map(p => p.name -> p).toMap

  final class ToolError(msg: String) extends RuntimeException(msg)

  private def schema(props: (String, Json)*)(required: String*): Json =
    obj("type" -> str("object"), "properties" -> JObj(props), "required" -> JArr(required.map(str)), "additionalProperties" -> JBool(false))
  private val project = "project" -> obj("type" -> str("string"), "description" -> str("Project name (optional when there is one project)."))
  private val node = "node" -> obj("type" -> str("string"), "description" -> str("Node id, as in the tree."))
  private def tool(name: String, description: String, input: Json) =
    obj("name" -> str(name), "description" -> str(description), "inputSchema" -> input)

  val tools: List[Json] = List(
    tool("inbox", "Start here. The developer's open requests (answer them by proposing nodes, then `answer`), rejected nodes " +
      "to remove from the Scala model, and decisions the developer has not made yet.", schema(project)()),
    tool("context", "Everything known about a node: the idea, the path from the root with every decision, reason and rejected " +
      "alternative, examples, the obligation, and open requests. Read it before proposing or changing a node.", schema(project, node)("node")),
    tool("render", "Rebuild from the Scala definitions: the Lean and the snapshot the browser shows. Run it after changing a node, " +
      "the domain or IDEA.md. Returns the tree; compile errors in the model come back as the error.", schema(project)()),
    tool("check", "Render, then prove each node's link to its parent in Lean and record the results. Slow (minutes). " +
      "Optionally one node.", schema(project, node)()),
    tool("answer", "Reply to a developer's request once done, e.g. 'Proposed Expiring and Sliding under Authenticated; " +
      "Expiring is simpler, Sliding keeps active users signed in. Choose in the browser.'",
      schema(project, "request" -> obj("type" -> str("string")), "text" -> obj("type" -> str("string")))("request", "text")),
    tool("scaffold", "Create lean/Proofs/<KB>/<NODE>.lean for an obligation frflow_auto did not prove. The proof must state " +
      "exactly `Obl.link` and contain only tactics.", schema(project, node)("node"))
  )

  private def projectOf(args: Json): Project = args("project").flatMap(_.str) match
    case None if projects.size == 1 => projects.head
    case None => throw ToolError(s"several projects; pass project, one of: ${byName.keys.mkString(", ")}")
    case Some(n) => byName.getOrElse(n, throw ToolError(s"unknown project $n; one of: ${byName.keys.mkString(", ")}"))

  private def staleness(p: Project): String =
    val c = p.sourcesChanged
    if c.isEmpty then "" else s"\n\nSources changed since this snapshot (${c.take(5).mkString(", ")}); call render."

  private def run(p: Project, args: List[String]): (String, Boolean) =
    val r = p.run(args, actor = "agent")
    (if r.output.nonEmpty then r.output else s"(exit code ${r.exitCode})", !r.ok)

  def call(name: String, args: Json): (String, Boolean) =
    val p = projectOf(args)
    val nodeArg = args("node").flatMap(_.str)
    nodeArg.filterNot(Project.Ident.matches).foreach(n => throw ToolError(s"not a node id: $n"))
    def need = nodeArg.getOrElse(throw ToolError("node is required"))
    name match
      case "render" =>
        val (out, err) = run(p, List("render"))
        if err then (out, true) else (out + p.annotated.fold("")(s => "\n\n" + frflow.Decisions.tree(s)), false)
      case "check"              => run(p, "check" :: nodeArg.toList)
      case "context" | "scaffold" => run(p, List(name, need))
      case "answer" =>
        try
          val r = p.answerRequest(args("request").flatMap(_.str).getOrElse(""), args("text").flatMap(_.str).getOrElse(""))
          (s"answered ${r("id").flatMap(_.str).getOrElse("")}", false)
        catch case e: java.util.NoSuchElementException => throw ToolError(e.getMessage)
      case "inbox" =>
        val open = p.requests.filter(_("status").flatMap(_.str).contains("open"))
        def f(r: Json, k: String) = r(k).flatMap(_.str).getOrElse("")
        val reqs =
          if open.isEmpty then List("No open requests.")
          else "Open requests from the developer:" :: open.map(r =>
            s"- [${f(r, "id")}] on ${if f(r, "node").isEmpty then "(the idea)" else f(r, "node")}: ${f(r, "text")}")
        val rest = p.annotated.fold(List("", "No snapshot yet; call render.")) { s =>
          val (dev, agent) = frflow.Decisions.waiting(s)
          (if agent.isEmpty then Nil else "" :: "For you:" :: agent.map("- " + _)) ++
            (if dev.isEmpty then Nil else "" :: "Waiting for the developer's decision (in the browser):" :: dev.map("- " + _))
        }
        val tree = p.annotated.fold("")(s => "\n\nThe tree:\n" + frflow.Decisions.tree(s))
        ((reqs ++ rest).mkString("\n") + tree + staleness(p), false)
      case other => throw ToolError(s"unknown tool $other")

  /** Handles one JSON-RPC message; None for notifications. */
  def handle(msg: Json): Option[Json] =
    val id = msg("id")
    val params = msg("params").getOrElse(obj())
    def result(v: Json) = Some(obj("jsonrpc" -> str("2.0"), "id" -> id.getOrElse(JNull), "result" -> v))
    msg("method").flatMap(_.str) match
      case Some("initialize") => result(obj(
          "protocolVersion" -> params("protocolVersion").getOrElse(str("2025-06-18")),
          "capabilities" -> obj("tools" -> obj("listChanged" -> JBool(false))),
          "serverInfo" -> obj("name" -> str("frflow"), "version" -> str("0.2.0")),
          "instructions" -> str(s"FrFlow knowledge bases: ${byName.keys.mkString(", ")}. The developer decides in the browser; " +
            "you propose nodes and answer requests. Start with inbox.")))
      case Some("ping")       => result(obj())
      case Some("tools/list") => result(obj("tools" -> JArr(tools)))
      case Some("tools/call") =>
        val (text, isError) =
          try call(params("name").flatMap(_.str).getOrElse(""), params("arguments").getOrElse(obj()))
          catch
            case e: ToolError => (e.getMessage, true)
            case e: Exception => (s"${e.getClass.getSimpleName}: ${e.getMessage}", true)
        result(obj("content" -> JArr(Seq(obj("type" -> str("text"), "text" -> str(text)))), "isError" -> JBool(isError)))
      case _ if id.isEmpty => None
      case other => Some(obj("jsonrpc" -> str("2.0"), "id" -> id.get,
          "error" -> obj("code" -> JNum(-32601), "message" -> str(s"method not found: ${other.getOrElse("")}"))))

  def serve(in: java.io.InputStream, out: PrintStream): Unit =
    val reader = BufferedReader(InputStreamReader(in, UTF_8))
    Iterator.continually(reader.readLine()).takeWhile(_ != null).map(_.trim).filter(_.nonEmpty).foreach { line =>
      val reply =
        try handle(Json.parse(line))
        catch case _: Json.ParseError => Some(obj("jsonrpc" -> str("2.0"), "id" -> JNull, "error" -> obj("code" -> JNum(-32700), "message" -> str("parse error"))))
      reply.foreach { r => out.println(r.compact); out.flush() }
    }

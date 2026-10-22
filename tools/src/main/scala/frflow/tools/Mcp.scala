package frflow.tools

import frflow.Json
import frflow.Json.*
import java.io.{BufferedReader, InputStreamReader, PrintStream}
import java.nio.charset.StandardCharsets.UTF_8

/** The FrFlow MCP server (stdio): how an agent works on a knowledge base.
  *
  * Tools run the knowledge base's CLI, which builds everything from the Scala
  * definitions. The agent proposes nodes and answers the developer's requests. Choices are the
  * developer's, in the browser: the agent never writes the ledger.
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
      "with who rejected them and why (propose what a reason asks for, or remove the node), decisions the developer has not made yet, and the tree from the root (each node under its " +
      "first parent, \"also under\" its others; the definitions apart).", schema(project)()),
    tool("context", "Everything known about a node: its idea section, the vocabulary it uses (terms, meanings, definitions in force), " +
      "the nodes above it through every parent with every decision, reason and rejected alternative, for each parent its co-parts, its parts, " +
      "examples, its obligations, and open requests. Read it before proposing or changing a node: a new statement goes under the lowest " +
      "nodes it helps prove, as a part; never as a restatement of its parent.", schema(project, node)("node")),
    tool("render", "Rebuild from the Scala definitions: the Lean and the snapshot the browser shows. Run it after changing a node, " +
      "the domain or IDEA.md. Returns the tree; compile errors in the model come back as the error.", schema(project)()),
    tool("check", "Render, then prove in Lean that each node's parts make it (complete), that each part is needed, that they do " +
      "not clash, and the root of the code (root_impl), and record the results. Slow (minutes). Optionally one node.", schema(project, node)()),
    tool("answer", "Reply to a developer's request once done, e.g. 'Proposed SlidingSessions, which replaces ExpiringSessions " +
      "(an alternative: accepting one rejects the other); Expiring is simpler, Sliding keeps active users signed in. Choose in the browser.' " +
      "Without a request, pass `node` " +
      "to tell the developer about work they did not ask for (a node to revisit, a change you made).",
      schema(project, "request" -> obj("type" -> str("string")), "node" -> obj("type" -> str("string")), "text" -> obj("type" -> str("string")))("text")),
    tool("find", "Where a change belongs: the nodes that govern a file (pass a path relative to the project), or the nodes " +
      "whose id, statement or reason mention some words. Extend those nodes rather than adding a near-duplicate.",
      schema(project, "query" -> obj("type" -> str("string")))("query")),
    tool("scaffold", "Create lean/Proofs/<KB>/<NODE>.lean for an obligation frflow_auto did not prove. The proof must state " +
      "exactly its `Obl` (`Obl.complete`, `Obl.impl`, ...) and contain only tactics.", schema(project, node)("node"))
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
          val text = args("text").flatMap(_.str).getOrElse("")
          val r = args("request").flatMap(_.str).filter(_.nonEmpty) match
            case Some(id) => p.answerRequest(id, text)
            case None =>
              val node = args("node").flatMap(_.str).getOrElse("")
              if node.nonEmpty && !Project.Ident.matches(node) then throw ToolError("expected a node id")
              // The developer's open request on the node, if there is one, is what this answers.
              val open = p.requests.find(q => q("node").flatMap(_.str).contains(node) && q("status").flatMap(_.str).contains("open"))
              val q = open.getOrElse(p.addRequest(node, "(from the agent)", "agent"))
              p.answerRequest(q("id").flatMap(_.str).get, text)
          (s"answered ${r("id").flatMap(_.str).getOrElse("")}", false)
        catch case e: java.util.NoSuchElementException => throw ToolError(e.getMessage)
      case "find" =>
        val q = args("query").flatMap(_.str).getOrElse("").trim
        if q.isEmpty then throw ToolError("query is required")
        p.annotated.fold(("No snapshot yet; call render.", true))(s => (frflow.Decisions.find(s, q), false))
      case "inbox" =>
        (frflow.Decisions.inbox(p.annotated, p.requests) + staleness(p), false)
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

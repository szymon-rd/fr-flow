package frflow.tools

import com.sun.net.httpserver.{HttpExchange, HttpServer}
import frflow.Json
import frflow.Json.*
import java.net.{InetSocketAddress, URI}
import java.nio.charset.StandardCharsets.UTF_8
import java.nio.file.Files
import java.util.concurrent.Executors

/** The FrFlow browser: where the developer reads the tree and makes decisions.
  *
  * The tree comes from `.frflow/kb.json`, written by the knowledge base's CLI from the
  * Scala definitions. Open pages update when the snapshot, the event log, the
  * requests or the sources change.
  *
  * {{{
  * GET  /api/projects
  * GET  /api/p/NAME/kb                       snapshot, sourcesChanged, running, requests
  * GET  /api/p/NAME/events?limit=N
  * GET  /api/p/NAME/job                      the last command started here
  * POST /api/p/NAME/run      {"args": [...]} render / check / scaffold
  * POST /api/p/NAME/decide   {"action", "node", "by", "reason", "reject", "subtree"}   the developer's decision
  * POST /api/p/NAME/requests {"node", "text", "by"}
  * POST /api/p/NAME/requests/ID {"status", "answer"}
  * POST /api/p/NAME/idea     {"text"}        saves IDEA.md, then renders
  * GET  /api/stream                          server-sent events on every change
  * }}}
  */
final class Server(projects: List[Project]):
  private val byName = projects.map(p => p.name -> p).toMap

  final class Job(val args: List[String]):
    val started: Long = System.currentTimeMillis
    @volatile var finished: Option[Long] = None
    @volatile var exitCode: Option[Int] = None
    @volatile var output: String = ""
    def json: Json = obj(
      "args" -> JArr(args.map(str)), "running" -> JBool(finished.isEmpty),
      "exitCode" -> exitCode.fold(JNull)(c => JNum(c.toDouble)), "output" -> str(output))

  private val jobs = scala.collection.concurrent.TrieMap.empty[String, Job]
  private val changed = Object()
  @volatile private var tick = 0L

  private def signal(): Unit = changed.synchronized { tick += 1; changed.notifyAll() }

  def start(p: Project, args: List[String]): Job = synchronized {
    jobs.get(p.name).filter(_.finished.isEmpty).foreach(j => throw IllegalStateException(s"${j.args.mkString(" ")} is still running"))
    val job = Job(args)
    jobs(p.name) = job
    Thread(() => {
      try
        val r = p.run(args, actor = "ui")
        job.output = r.output; job.exitCode = Some(r.exitCode)
      catch case e: Exception => { job.output = s"${e.getClass.getSimpleName}: ${e.getMessage}"; job.exitCode = Some(1) }
      job.finished = Some(System.currentTimeMillis)
      signal()
    }).start()
    signal()
    job
  }

  /** Notifies open pages when anything they show changes. */
  private def watch(): Unit =
    val versions = scala.collection.mutable.Map.empty[String, String]
    while true do
      projects.foreach { p =>
        val v = p.version
        if !versions.get(p.name).contains(v) then { versions(p.name) = v; signal() }
      }
      Thread.sleep(500)

  // -- HTTP ---------------------------------------------------------------------

  private def send(ex: HttpExchange, status: Int, body: Array[Byte], ctype: String): Unit =
    ex.getResponseHeaders.set("Content-Type", ctype)
    ex.getResponseHeaders.set("Cache-Control", "no-store")
    ex.sendResponseHeaders(status, if body.isEmpty then -1 else body.length.toLong)
    if body.nonEmpty then ex.getResponseBody.write(body)
    ex.close()

  private def json(ex: HttpExchange, v: Json, status: Int = 200): Unit =
    send(ex, status, v.compact.getBytes(UTF_8), "application/json; charset=utf-8")

  private def error(ex: HttpExchange, status: Int, msg: String): Unit = json(ex, obj("error" -> str(msg)), status)

  /** Why a command from the browser is refused, if it is. */
  def refuse(args: List[String]): Option[String] =
    def id(s: String) = Project.Ident.matches(s)
    args match
      case "render" :: Nil                                => None
      case "check" :: rest if rest.size <= 1 && rest.forall(id) => None
      case "scaffold" :: n :: Nil if id(n)                => None
      case _ => Some("expected render, check [NODE] or scaffold NODE")

  private def get(ex: HttpExchange, parts: List[String], query: Map[String, String]): Unit = parts match
    case Nil | List("index.html") =>
      val ui = getClass.getResourceAsStream("/frflow/ui/index.html")
      send(ex, 200, ui.readAllBytes(), "text/html; charset=utf-8")
    case List("api", "projects") =>
      json(ex, JArr(projects.map(p => obj("name" -> str(p.name), "running" -> p.running.getOrElse(JNull)))))
    case List("api", "stream") => stream(ex)
    case List("api", "p", name, what) =>
      byName.get(name) match
        case None => error(ex, 404, s"unknown project $name")
        case Some(p) => what match
          case "kb" => json(ex, obj("snapshot" -> p.annotated.getOrElse(JNull), "sourcesChanged" -> JArr(p.sourcesChanged.map(str)),
              "running" -> p.running.getOrElse(JNull), "requests" -> JArr(p.requests)))
          case "events" => json(ex, JArr(p.events(query.get("limit").flatMap(_.toIntOption).getOrElse(500))))
          case "job"    => json(ex, jobs.get(p.name).fold(JNull)(_.json))
          case _        => error(ex, 404, "not found")
    case _ => error(ex, 404, "not found")

  private def post(ex: HttpExchange, parts: List[String]): Unit =
    // Only this page may change things: refuse requests sent by other sites.
    val origin = Option(ex.getRequestHeaders.getFirst("Origin"))
    val host = Option(ex.getRequestHeaders.getFirst("Host")).getOrElse("")
    if origin.exists(o => URI(o).getAuthority != host) then return error(ex, 403, "cross-origin request")
    if !Option(ex.getRequestHeaders.getFirst("Content-Type")).exists(_.startsWith("application/json")) then
      return error(ex, 415, "expected application/json")
    val body = try Json.parse(String(ex.getRequestBody.readAllBytes(), UTF_8)) catch case e: Exception => return error(ex, 400, s"bad JSON: ${e.getMessage}")
    def field(k: String) = body(k).flatMap(_.str).getOrElse("")
    parts match
      case "api" :: "p" :: name :: what if !byName.contains(name) => error(ex, 404, s"unknown project $name")
      case "api" :: "p" :: name :: what =>
        val p = byName(name)
        what match
          case List("run") =>
            val args = body("args").map(_.arr.toList).getOrElse(Nil).flatMap(_.str)
            refuse(args) match
              case Some(why) => error(ex, 400, why)
              case None =>
                try json(ex, start(p, args).json, 202) catch case e: IllegalStateException => error(ex, 409, e.getMessage)
          case List("decide") =>
            val req = frflow.Decisions.Request(field("action"), field("node"), field("by"), field("reason"),
              body("reject").map(_.arr.toList).getOrElse(Nil).flatMap(_.str), body("subtree").contains(JBool(true)))
            if !Project.Ident.matches(req.node) then error(ex, 400, "expected a node id")
            else p.decide(req, actor = "ui") match
              case Left(why) => error(ex, 409, why)
              case Right(()) => signal(); json(ex, obj("ok" -> JBool(true)))
          case List("requests") =>
            val (node, text, by) = (field("node"), field("text").trim, field("by").trim)
            if text.isEmpty || by.isEmpty || (node.nonEmpty && !Project.Ident.matches(node)) then error(ex, 400, "expected node, text and by")
            else { val r = p.addRequest(node, text, by); signal(); json(ex, r, 201) }
          case List("requests", id) =>
            try { val r = p.answerRequest(id, field("answer"), body("status").flatMap(_.str).getOrElse("closed")); signal(); json(ex, r) }
            catch case e: java.util.NoSuchElementException => error(ex, 404, e.getMessage)
          case List("idea") =>
            val text = field("text")
            if text.trim.isEmpty then error(ex, 400, "expected text")
            else
              Files.writeString(p.ideaFile, if text.endsWith("\n") then text else text + "\n", UTF_8)
              try json(ex, start(p, List("render")).json, 202) catch case e: IllegalStateException => error(ex, 409, s"saved; ${e.getMessage}")
          case _ => error(ex, 404, "not found")
      case _ => error(ex, 404, "not found")

  private def stream(ex: HttpExchange): Unit =
    ex.getResponseHeaders.set("Content-Type", "text/event-stream")
    ex.getResponseHeaders.set("Cache-Control", "no-store")
    ex.sendResponseHeaders(200, 0)
    val out = ex.getResponseBody
    var seen = -1L
    try
      while true do
        val now = changed.synchronized {
          if tick == seen then changed.wait(15000)
          tick
        }
        out.write((if now != seen then s"data: {\"tick\":$now}\n\n" else ": keep-alive\n\n").getBytes(UTF_8))
        out.flush()
        seen = now
    catch case _: java.io.IOException => ()
    finally ex.close()

  /** Starts serving; returns the bound port. */
  def serve(host: String, port: Int): HttpServer =
    val server = HttpServer.create(InetSocketAddress(host, port), 0)
    server.setExecutor(Executors.newCachedThreadPool(r => { val t = Thread(r); t.setDaemon(true); t }))
    server.createContext("/", ex =>
      try
        val uri = ex.getRequestURI
        val parts = uri.getPath.split("/").filter(_.nonEmpty).map(java.net.URLDecoder.decode(_, UTF_8)).toList
        val query = Option(uri.getRawQuery).toList.flatMap(_.split("&")).flatMap(_.split("=", 2) match
          case Array(k, v) => Some(k -> java.net.URLDecoder.decode(v, UTF_8))
          case _           => None).toMap
        ex.getRequestMethod match
          case "GET"  => get(ex, parts, query)
          case "POST" => post(ex, parts)
          case _      => error(ex, 405, "method not allowed")
      catch case e: Exception => try error(ex, 500, s"${e.getClass.getSimpleName}: ${e.getMessage}") catch case _: Exception => ()
    )
    val watcher = Thread(() => watch())
    watcher.setDaemon(true)
    watcher.start()
    server.start()
    server

package frflow.tools

import frflow.Json
import frflow.Json.*
import java.nio.channels.FileChannel
import java.nio.charset.StandardCharsets.UTF_8
import java.nio.file.{Files, Path, StandardCopyOption, StandardOpenOption}
import java.util.concurrent.{ConcurrentHashMap, TimeUnit}
import java.util.concurrent.locks.ReentrantLock
import scala.jdk.CollectionConverters.*

/** The outcome of running a knowledge base's CLI. */
final case class RunResult(command: List[String], exitCode: Int, output: String):
  def ok: Boolean = exitCode == 0

/** A FrFlow project: a directory with a `frflow.json`.
  *
  * {{{
  * { "name": "Auth", "run": ["sbt", "auth/run {args}"], "cwd": "../..",
  *   "sources": ["src/main/scala", "IDEA.md", "lean/Proofs"] }
  * }}}
  *
  * The knowledge base is defined in Scala. Its CLI (`render`, `check`, ...) writes
  * `.frflow/kb.json`, the snapshot of the definitions and the ledger, and appends to
  * `.frflow/events.jsonl`. The tools never build the tree themselves: they run the
  * CLI and read what it wrote. Requests (developer to agent) are kept here, in
  * `.frflow/requests.json`.
  */
final class Project(dir: Path):
  val root: Path = dir.toAbsolutePath.normalize
  val config: Json = Json.parse(Files.readString(root.resolve("frflow.json"), UTF_8))
  val name: String = config("name").flatMap(_.str).getOrElse(root.getFileName.toString)
  val state: Path = root.resolve(".frflow")

  def snapshotFile: Path = state.resolve("kb.json")
  def eventsFile: Path = state.resolve("events.jsonl")
  def runningFile: Path = state.resolve("running.json")
  def requestsFile: Path = state.resolve("requests.json")
  def ledgerFile: Path = state.resolve("ledger.json")
  def ideaFile: Path = root.resolve(config("idea").flatMap(_.str).getOrElse("IDEA.md"))

  private def readJson(p: Path): Option[Json] =
    try Some(Json.parse(Files.readString(p, UTF_8))) catch case _: Exception => None

  def snapshot: Option[Json] = readJson(snapshotFile)
  def ledger: frflow.Ledger = frflow.Ledger.load(ledgerFile)

  /** The snapshot with the developer's decisions, read now (see `frflow.Decisions`). */
  def annotated: Option[Json] = snapshot.map(frflow.Decisions.annotate(_, ledger))

  /** Records a developer's decision without running the CLI: the snapshot carries what is decided.
    * Refused when the sources changed since the snapshot, since the decision would bind to stale content.
    */
  def decide(r: frflow.Decisions.Request, actor: String): Either[String, Unit] =
    snapshot match
      case None => Left("no snapshot yet: render first")
      case Some(_) if sourcesChanged.nonEmpty => Left(s"the sources changed since the last render (${sourcesChanged.take(3).mkString(", ")}): render first")
      case Some(snap) =>
        Project.locked(state.resolve("ledger.lock")) {
          frflow.Decisions.decide(snap, ledger, r, java.time.Instant.now.toString).map { (l, events) =>
            frflow.Ledger.save(ledgerFile, l)
            val lines = events.map(e => JObj(e.obj :+ ("actor" -> str(actor))).compact + "\n").mkString
            Files.writeString(eventsFile, lines, UTF_8, StandardOpenOption.CREATE, StandardOpenOption.APPEND)
            ()
          }
        }
  def running: Option[Json] = readJson(runningFile)

  def events(limit: Int = 0): List[Json] =
    val all =
      if !Files.isRegularFile(eventsFile) then Nil
      else Files.readAllLines(eventsFile, UTF_8).asScala.toList.flatMap(l => try Some(Json.parse(l)) catch case _: Exception => None)
    if limit > 0 then all.takeRight(limit) else all

  // -- requests: what the developer asks the agent for --------------------------

  def requests: List[Json] = readJson(requestsFile).map(_.arr.toList).getOrElse(Nil)

  private def updateRequests[T](change: List[Json] => (List[Json], T)): T =
    Files.createDirectories(state)
    Project.locked(state.resolve("requests.lock")) {
      val (next, out) = change(requests)
      val tmp = state.resolve("requests.json.tmp")
      Files.writeString(tmp, JArr(next).render() + "\n", UTF_8)
      Files.move(tmp, requestsFile, StandardCopyOption.REPLACE_EXISTING, StandardCopyOption.ATOMIC_MOVE)
      out
    }

  def addRequest(node: String, text: String, by: String): Json = updateRequests { rs =>
    val r = obj("id" -> str(s"R${java.lang.Long.toString(System.currentTimeMillis, 36)}"), "node" -> str(node), "text" -> str(text), "by" -> str(by),
      "at" -> str(java.time.Instant.now.toString.take(19) + "Z"), "status" -> str("open"), "answer" -> str(""))
    (rs :+ r, r)
  }

  /** Records the agent's answer, or the developer closing a request. */
  def answerRequest(id: String, answer: String, status: String = "answered"): Json = updateRequests { rs =>
    val i = rs.indexWhere(_("id").flatMap(_.str).contains(id))
    if i < 0 then throw java.util.NoSuchElementException(s"unknown request $id")
    val keepAnswer = if answer.isEmpty then rs(i)("answer").getOrElse(str("")) else str(answer)
    val r = Project.set(Project.set(rs(i), "status", str(status)), "answer", keepAnswer)
    (rs.updated(i, r), r)
  }

  // -- sources ------------------------------------------------------------------

  def sourceFiles: List[Path] =
    config("sources").map(_.arr.toList).getOrElse(Nil).flatMap(_.str).map(root.resolve).flatMap { p =>
      if Files.isRegularFile(p) then List(p)
      else if Files.isDirectory(p) then Files.walk(p).iterator.asScala.filter(Files.isRegularFile(_)).toList
      else Nil
    }

  /** Sources modified after the snapshot was written: the tree may be out of date. */
  def sourcesChanged: List[String] =
    if !Files.isRegularFile(snapshotFile) then List("(no snapshot yet)")
    else
      val at = Files.getLastModifiedTime(snapshotFile).toMillis
      sourceFiles.filter(f => Files.getLastModifiedTime(f).toMillis > at).map(f => root.relativize(f).toString).sorted

  /** Changes whenever anything the browser shows changes. */
  def version: String =
    (List(snapshotFile, eventsFile, runningFile, requestsFile, ledgerFile) ++ sourceFiles).map { f =>
      if Files.exists(f) then s"$f:${Files.getLastModifiedTime(f).toMillis}:${Files.size(f)}" else s"$f:-"
    }.mkString("|")

  // -- running the CLI ----------------------------------------------------------

  def command(args: List[String]): List[String] =
    val joined = args.map(Project.quote).mkString(" ")
    config("run").map(_.arr.toList).getOrElse(Nil).flatMap(_.str).map(_.replace("{args}", joined))

  /** Runs the CLI. One command at a time per project, across processes. */
  def run(args: List[String], actor: String, timeoutSeconds: Long = 3600): RunResult =
    require(args.headOption.exists(Project.Commands.contains), s"unknown command ${args.headOption.getOrElse("")}")
    val cmd = command(args)
    val cwd = root.resolve(config("cwd").flatMap(_.str).getOrElse(".")).normalize
    Files.createDirectories(state)
    Project.locked(state.resolve("run.lock")) {
      Files.writeString(runningFile, obj("args" -> JArr(args.map(str)), "actor" -> str(actor)).compact, UTF_8)
      try
        val pb = ProcessBuilder(cmd*).directory(cwd.toFile).redirectErrorStream(true)
          .redirectInput(ProcessBuilder.Redirect.from(java.io.File("/dev/null")))
        pb.environment.put("FRFLOW_ACTOR", actor)
        val proc = pb.start()
        val out = java.io.ByteArrayOutputStream()
        val pump = Thread(() => { proc.getInputStream.transferTo(out); () })
        pump.start()
        if !proc.waitFor(timeoutSeconds, TimeUnit.SECONDS) then
          proc.destroyForcibly(); pump.join(1000)
          RunResult(cmd, 124, Project.clean(out.toString(UTF_8)) + s"\ntimed out after ${timeoutSeconds}s")
        else
          pump.join()
          RunResult(cmd, proc.exitValue(), Project.clean(out.toString(UTF_8)))
      catch case e: java.io.IOException => RunResult(cmd, 127, s"cannot run ${cmd.mkString(" ")}: ${e.getMessage}")
      finally Files.deleteIfExists(runningFile)
    }

object Project:
  /** CLI commands, and whether an agent may run them. Deciding (`accept`) is the developer's. */
  val Commands: Map[String, Boolean] =
    Map("render" -> true, "check" -> true, "status" -> true, "context" -> true, "scaffold" -> true)

  val Ident: scala.util.matching.Regex = "[A-Za-z_][A-Za-z0-9_]*".r

  private val locks = ConcurrentHashMap[Path, ReentrantLock]()

  /** Runs `body` holding a lock on `file`, against threads of this process and other processes. */
  def locked[T](file: Path)(body: => T): T =
    val l = locks.computeIfAbsent(file.toAbsolutePath.normalize, _ => ReentrantLock())
    l.lock()
    try
      val ch = FileChannel.open(file, StandardOpenOption.CREATE, StandardOpenOption.WRITE)
      try
        val fl = ch.lock()
        try body finally fl.release()
      finally ch.close()
    finally l.unlock()

  def set(j: Json, key: String, v: Json): Json =
    val fs = j.obj
    if fs.exists(_._1 == key) then JObj(fs.map((k, x) => if k == key then k -> v else k -> x)) else JObj(fs :+ (key -> v))

  /** An argument as sbt's input parser reads it. */
  def quote(arg: String): String =
    if arg.nonEmpty && !arg.exists(c => c.isWhitespace || c == '"' || c == '\\' || c == ';') then arg
    else "\"" + arg.replace("\\", "\\\\").replace("\"", "\\\"") + "\""

  private val Noise =
    """^(Picked up JAVA_TOOL_OPTIONS|(\[info\] )?(welcome to sbt|loading |set current project|running \(fork\)|compiling |done compiling|Fetching)|\[success\] Total time).*""".r

  /** The CLI's output without sbt's noise and prefixes. */
  def clean(text: String): String =
    text.linesIterator.map(l => if l.startsWith("[info] ") then l.drop(7) else if l.startsWith("[error] ") then l.drop(8) else l)
      .filterNot(l => Noise.matches(l)).mkString("\n").stripPrefix("\n").stripSuffix("\n")

  private def s(j: Json, k: String): String = j(k).flatMap(_.str).getOrElse("")

  /** A compact text tree of an annotated snapshot: decision state, link to parent, examples. */
  def tree(snapshot: Json): String =
    val nodes = snapshot("nodes").map(_.arr.toList).getOrElse(Nil)
    def parent(n: Json) = n("parent").flatMap(_.str)
    def go(n: Json, depth: Int): List[String] =
      val link = n("link").filter(_ != JNull).fold("") { l =>
        val d = s(l, "detail")
        s"link ${s(l, "status")}${if d.nonEmpty then s" ($d)" else ""}, "
      }
      val ex = n("examples").map(_.arr.toList).getOrElse(Nil)
      val bad = ex.count(e => s(e, "contract") != "ok" || e("implementation").exists(i => i != JNull && !i.str.contains("ok")))
      val exs = if ex.isEmpty then "" else s", examples ${ex.size - bad}/${ex.size}"
      val code = if n("codeChanged").contains(JBool(true)) then ", code changed" else ""
      s"${"  " * depth}${s(n, "id")} (${s(n, "kind")})  [${s(n, "state")}$code${if link.isEmpty then "" else ", " + link.stripSuffix(", ")}$exs]" ::
        nodes.filter(c => parent(c).contains(s(n, "id"))).flatMap(go(_, depth + 1))
    val removed = snapshot("removed").map(_.arr.toList).getOrElse(Nil).map(r => s"${s(r, "id")}  [removed from the model]")
    (nodes.filter(parent(_).isEmpty).flatMap(go(_, 0)) ++ removed).mkString("\n")

  /** What waits on whom, in an annotated snapshot: decisions for the developer, clean-up for the agent. */
  def waiting(snapshot: Json): (List[String], List[String]) =
    val nodes = snapshot("nodes").map(_.arr.toList).getOrElse(Nil)
    val dev = nodes.filter(n => Set("proposed", "changed", "parent-changed")(s(n, "state"))).map(n => s"${s(n, "id")}: ${s(n, "state")}") ++
      nodes.filter(_("codeChanged").contains(JBool(true))).map(n => s"${s(n, "id")}: its code changed since it was decided") ++
      snapshot("removed").map(_.arr.toList).getOrElse(Nil).map(r => s"${s(r, "id")}: removed from the model; confirm the removal")
    val agent = nodes.filter(n => s(n, "state") == "rejected").map(n => s"${s(n, "id")}: rejected; remove it from the Scala model")
    (dev, agent)

  /** Projects at the given paths; a directory without `frflow.json` is searched one level down. */
  def find(paths: List[String]): List[Project] =
    val ps = paths.map(Path.of(_)).flatMap { d =>
      if Files.isRegularFile(d.resolve("frflow.json")) then List(Project(d))
      else if Files.isDirectory(d) then
        Files.list(d).iterator.asScala.toList.sortBy(_.toString).filter(c => Files.isRegularFile(c.resolve("frflow.json"))).map(Project(_))
      else Nil
    }
    val dup = ps.groupBy(_.name).collect { case (n, xs) if xs.size > 1 => n }
    require(dup.isEmpty, s"duplicate project names: ${dup.mkString(", ")}")
    ps

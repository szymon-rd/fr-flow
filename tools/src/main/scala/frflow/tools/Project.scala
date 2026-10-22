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
  * { "name": "Auth", "run": ["sbt", "--client", "auth/run {args}"], "cwd": "../..",
  *   "sources": ["src/main/scala", "IDEA.md", "lean/Proofs"] }
  * }}}
  *
  * The knowledge base is defined in Scala. Its CLI (`render`, `check`, ...) writes
  * `.frflow/kb.json`, the snapshot of the definitions. `.frflow/ledger.json` holds the
  * developer's decisions. The tools never build the tree themselves: they run the CLI
  * and read what it wrote. Requests (developer to agent) are kept here, in
  * `.frflow/requests.json`.
  */
final class Project(dir: Path):
  val root: Path = dir.toAbsolutePath.normalize
  val config: Json = Json.parse(Files.readString(root.resolve("frflow.json"), UTF_8))
  val name: String = config("name").flatMap(_.str).getOrElse(root.getFileName.toString)
  val state: Path = root.resolve(".frflow")

  def snapshotFile: Path = state.resolve("kb.json")
  def runningFile: Path = state.resolve("running.json")
  def requestsFile: Path = state.resolve("requests.json")
  def ledgerFile: Path = state.resolve("ledger.json")
  def ideaFile: Path = root.resolve(snapshot.flatMap(_("ideaFile")).flatMap(_.str).getOrElse("IDEA.md"))

  private def readJson(p: Path): Option[Json] =
    try Some(Json.parse(Files.readString(p, UTF_8))) catch case _: Exception => None

  def snapshot: Option[Json] = readJson(snapshotFile)
  def ledger: frflow.Ledger = frflow.Ledger.load(ledgerFile)

  /** The snapshot with the developer's decisions, read now (see `frflow.Decisions`), and warnings
    * if committed decisions were rewritten since.
    */
  def annotated: Option[Json] = snapshot.map { s =>
    val l = ledger
    val restarts = frflow.Ledger.toAcknowledge(root, ledgerFile, l)
    val a = frflow.Decisions.annotate(s, l)
    val warnings = frflow.Ledger.warnings(root, ledgerFile, l).map(str) ++ a("warnings").map(_.arr.toList).getOrElse(Nil)
    JObj(a.obj.filterNot(f => f._1 == "warnings" || f._1 == "restarts") :+ ("warnings" -> JArr(warnings)) :+
      ("restarts" -> JArr(restarts.map((c, why) => obj("commit" -> str(c), "why" -> str(why))))) :+ ("unsigned" -> JArr(unsigned)) :+
      ("keys" -> keyState))
  }

  /** How the code a node governs changed since the developer decided it (a git diff). */
  def codeDiff(node: String): String =
    val n = snapshot.flatMap(_("nodes")).map(_.arr).getOrElse(Nil).find(_("id").flatMap(_.str).contains(node))
    val files = n.flatMap(_("code")).flatMap(_("files")).map(_.arr.toList.flatMap(_.str)).getOrElse(Nil)
    // Against the code as decided; a clone without that tree falls back to the commit checked out then.
    // Never decided: the whole of each file, so what is accepted is seen.
    ledger.binding(node) match
      case None => files.map(f => root.resolve(f)).filter(Files.isRegularFile(_))
          .map(f => s"--- ${root.relativize(f)} (in full)\n" + Files.readString(f, UTF_8)).mkString("\n")
      case Some(d) =>
        val since = if frflow.Git.has(root, d.tree) then d.tree else d.commit
        if since.isEmpty || files.isEmpty then "" else
          val d = frflow.Git.diff(root, since, files)
          val notes = snapshot.toList.flatMap(frflow.Decisions.codeNotes(_, d))
          (if notes.isEmpty then "" else notes.map("# note: " + _).mkString("", "\n", "\n")) + d

  /** Saves IDEA.md; a render brings the snapshot up to date. */
  def saveIdea(text: String): Unit =
    Files.writeString(ideaFile, if text.endsWith("\n") then text else text + "\n", UTF_8)

  /** Records a developer's decision without running the CLI: the snapshot carries what is decided,
    * and the decision binds what the developer saw in it (a node that moved since is refused by
    * `seen`). Edits elsewhere in the sources do not hold it up; edits to the code the node governs do,
    * since the decision records that code as seen.
    */
  def decide(r: frflow.Decisions.Request): Either[String, Unit] =
    snapshot match
      case None => Left("no snapshot yet: render first")
      case Some(snap) if !snap("format").contains(JNum(frflow.Workflow.ContentFormat)) =>
        Left("the snapshot was written by another version of FrFlow: render first")
      case Some(snap) if (r.node :: r.confirm ++ r.revisit).exists(codeMoved(snap, _)) =>
        Left(s"the code governed by ${(r.node :: r.confirm ++ r.revisit).filter(codeMoved(snap, _)).mkString(", ")} changed since the last render: render first")
      case Some(snap) =>
        Project.locked(state.resolve("ledger.lock")) {
          val files = snap("nodes").map(_.arr.toList).getOrElse(Nil).flatMap(_("code")).flatMap(_("files")).flatMap(_.arr).flatMap(_.str).distinct
          val before = ledger
          frflow.Decisions.decide(snap, before, r, java.time.Instant.now.toString, frflow.Git.head(root), frflow.Git.snapshot(root, files))
            .map(l => frflow.Ledger.save(ledgerFile, signed(before, l)))
        }

  /** The developer's new decisions, signed when this process holds the developer's key (the browser
    * server does; the MCP server does not), with the public key published in `.frflow/keys`.
    */
  private def signed(before: frflow.Ledger, now: frflow.Ledger): frflow.Ledger =
    Project.signingKey.fold(now) { (priv, pub) =>
      frflow.Signing.publish(pub, state.resolve("keys"))
      frflow.Signing.signNew(before, now, priv, pub)
    }

  /** The developer's decisions not signed by a known key, for the developer to look at. */
  def unsigned: List[Json] =
    frflow.Signing.unsigned(ledger, state.resolve("keys")).map((id, d) => obj(
      "node" -> str(id), "entry" -> str(frflow.Ledger.entry(d)), "action" -> str(d.action), "by" -> str(d.by), "at" -> str(d.at),
      "reason" -> str(d.reason)))

  /** This process's key, whether it is a developer key of the project, and the keys that are not. */
  def keyState: Json =
    val dir = state.resolve("keys")
    val trusted = frflow.Signing.keys(dir)
    obj("mine" -> Project.signingKey.fold(JNull)((_, pub) => str(frflow.Signing.keyId(pub))),
      "mineTrusted" -> JBool(Project.signingKey.exists((_, pub) => trusted.contains(frflow.Signing.keyId(pub)))),
      "untrusted" -> JArr(frflow.Signing.keyFiles(dir).filterNot(k => trusted.contains(k.id)).map(k => str(k.id))))

  /** Certifies another key with this process's developer key. */
  def certify(id: String): Either[String, Unit] =
    Project.signingKey.toRight("this process holds no developer key").flatMap((priv, pub) => frflow.Signing.certify(state.resolve("keys"), id, priv, pub))

  /** Signs the named decisions with the developer's key: the developer says they are theirs. */
  def sign(entries: Set[String]): Either[String, Unit] =
    Project.signingKey match
      case None => Left("this process holds no developer key")
      case Some((priv, pub)) =>
        Project.locked(state.resolve("ledger.lock")) {
          frflow.Signing.publish(pub, state.resolve("keys"))
          frflow.Ledger.save(ledgerFile, frflow.Signing.signEntries(ledger, entries, priv, pub))
        }
        Right(())

  /** Whether the files a node governs differ from what the snapshot saw (file times can lie). */
  private def codeMoved(snap: Json, node: String): Boolean =
    snap("nodes").map(_.arr.toList).getOrElse(Nil).find(_("id").flatMap(_.str).contains(node)).flatMap(_("code")).filter(_ != JNull)
      .exists { c =>
        val files = c("files").map(_.arr.toList.flatMap(_.str)).getOrElse(Nil)
        frflow.Code.of(root, files.map(root.resolve)).fingerprint != c("fingerprint").flatMap(_.str).getOrElse("")
      }

  /** The command running now, if any (from this or another process). */
  def running: Option[Json] = readJson(runningFile)

  /** Every decision, newest first. */
  def history: Json = frflow.Decisions.history(ledger)

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
    (List(snapshotFile, runningFile, requestsFile, ledgerFile) ++ sourceFiles).map { f =>
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
        // The CLI's output is read as UTF-8; make sure it writes UTF-8 whatever the locale.
        if !Option(pb.environment.get("LC_ALL")).exists(_.toUpperCase.contains("UTF")) then pb.environment.put("LC_ALL", "C.UTF-8")
        pb.environment.put("JAVA_TOOL_OPTIONS", (Option(pb.environment.get("JAVA_TOOL_OPTIONS")).getOrElse("") + " -Dstdout.encoding=UTF-8 -Dfile.encoding=UTF-8").trim)
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
  /** The developer's signing key, held by the browser server only (see `frflow.Signing`). */
  @volatile var signingKey: Option[(java.security.PrivateKey, java.security.PublicKey)] = None

  /** Where the browser server keeps the developer's key: outside every repository. */
  def keyFile: Path = sys.env.get("FRFLOW_KEY").map(Path.of(_))
    .getOrElse(Path.of(sys.props("user.home"), ".config", "frflow", "signing.key"))
  /** The CLI commands the tools run. Deciding (`accept`) is the developer's, through `decide`. */
  val Commands: Set[String] = Set("render", "check", "status", "context", "scaffold")

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
    """^(Picked up JAVA_TOOL_OPTIONS|> |(\[info\] )?(welcome to sbt|loading |set current project|running \(fork\)|compiling |done compiling|Fetching|entering \*experimental\* thin client|server was not detected|terminate the server with)|\[success\] Total time).*""".r
  private val Ansi = """\u001b\[[0-9;]*m""".r

  /** The CLI's output without sbt's noise and prefixes. */
  def clean(text: String): String =
    Ansi.replaceAllIn(text, "").linesIterator.map(l => if l.startsWith("[info] ") then l.drop(7) else if l.startsWith("[error] ") then l.drop(8) else l)
      .filterNot(l => Noise.matches(l)).mkString("\n").stripPrefix("\n").stripSuffix("\n")

  private def s(j: Json, k: String): String = j(k).flatMap(_.str).getOrElse("")

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

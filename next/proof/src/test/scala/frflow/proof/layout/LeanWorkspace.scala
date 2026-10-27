package frflow.proof.layout

import frflow.proof.lean.ast.{LeanModule, Names}
import frflow.proof.lean.print.Print
import java.nio.file.{Files, Path}
import java.util.concurrent.TimeUnit
import scala.jdk.CollectionConverters.*

/** A Lake project in a temporary directory holding generated modules, built against FrFlow's Lean library
  * (`next/proof/lean`): what the `Lean`-tagged suites run Lean on.
  */
final class LeanWorkspace(val dir: Path):
  /** Writes the modules (and a root importing each), and builds them: Lake's output, and whether it built. */
  def build(modules: List[LeanModule], minutes: Int = 10): (Boolean, String) =
    modules.foreach(m => write(m.name.file.value.stripPrefix("lean/"), Print.module(m)))
    write("FrFlowGen.lean", modules.map(m => s"import ${m.name.dotted}\n").mkString)
    LeanWorkspace.libraryBuilt match
      case (true, _)    => LeanWorkspace.lake(dir, minutes)
      case (false, out) => (false, s"FrFlow's Lean library does not build:\n$out")

  def write(rel: String, text: String): Unit =
    val f = dir.resolve(rel)
    Files.createDirectories(f.getParent)
    val _ = Files.writeString(f, text)

object LeanWorkspace:
  /** FrFlow's Lean library, from the build's directory or the module's. */
  def library: Path =
    val here = Path.of(sys.props("user.dir")).toAbsolutePath
    List(here.resolve("next/proof/lean"), here.resolve("lean")).find(p => Files.exists(p.resolve("FrFlow.lean")))
      .getOrElse(throw IllegalStateException(s"FrFlow's Lean library is not under $here"))

  /** `lake build` in `dir`: whether it built, and Lake's output. */
  def lake(dir: Path, minutes: Int): (Boolean, String) =
    val p = ProcessBuilder("lake", "build").directory(dir.toFile).redirectErrorStream(true).start()
    given scala.concurrent.ExecutionContext = scala.concurrent.ExecutionContext.global
    val out = scala.concurrent.Future(String(p.getInputStream.readAllBytes()))
    val ended = p.waitFor(minutes.toLong, TimeUnit.MINUTES)
    if !ended then p.destroyForcibly(): Unit
    (ended && p.exitValue == 0, scala.concurrent.Await.result(out, scala.concurrent.duration.Duration(1, "minute")))

  /** FrFlow's library built once, before any workspace reads it. Every workspace requires it by path, and Lake builds a
    * path dependency in its own directory: two workspaces building it at once (the suites run in parallel, and the
    * library is stale after a change to it) race on its files ("no such file or directory"). Built here first, under
    * a lock on a file another JVM's suites take too, each workspace only reads it.
    */
  lazy val libraryBuilt: (Boolean, String) =
    val lock = library.resolve(".lake").resolve("suites.lock")
    Files.createDirectories(lock.getParent)
    val channel = java.nio.channels.FileChannel.open(lock, java.nio.file.StandardOpenOption.CREATE,
      java.nio.file.StandardOpenOption.WRITE)
    try
      val held = channel.lock()
      try lake(library, 10)
      finally held.release()
    finally channel.close()

  def make(name: String): LeanWorkspace =
    val dir = Files.createTempDirectory(s"frflow-$name")
    val w = LeanWorkspace(dir)
    w.write("lakefile.toml", s"""name = "${Names.builtin(name).text}"
      |defaultTargets = ["FrFlowGen"]
      |
      |[[require]]
      |name = "frflow"
      |path = "${library.toString.replace("\\", "/")}"
      |
      |[[lean_lib]]
      |name = "FrFlowGen"
      |""".stripMargin)
    w.write("lean-toolchain", Files.readString(library.resolve("lean-toolchain")))
    w

  /** The files under a workspace, for a failing test's message. */
  def files(w: LeanWorkspace): List[String] =
    Files.walk(w.dir).iterator.asScala.filter(Files.isRegularFile(_)).map(w.dir.relativize(_).toString).toList.sorted

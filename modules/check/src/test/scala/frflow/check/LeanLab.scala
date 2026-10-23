package frflow
package check

import cats.effect.unsafe.implicits.global
import frflow.lean.*
import frflow.protocol.*
import java.nio.file.{Files, Path, Paths}

/** End to end against Lean: each test in a fresh workspace. Every test is tagged `Lean`: plain `sbt test` leaves them
  * out, `sbt leanTest` runs them (the suites in parallel). Skipped when `lake` is not available.
  */
trait LeanLab extends munit.FunSuite with TempDirs:

  override val munitTimeout = scala.concurrent.duration.Duration(30, "min")
  override def munitTests(): Seq[Test] = super.munitTests().map(_.tag(LeanLab.Lean))

  protected lazy val kernel: Path = LeanLab.kernel

  protected def lake(dir: Path): Lake = Config.load.flatMap(Lake(dir, _)).unsafeRunSync()
  protected def lakeAvailable: Boolean = LeanLab.available

  /** A workflow in a fresh workspace, its operations run one after another. */
  protected final class Lab(w: OnDisk):
    def ws: Workspace = w.ws
    def check(only: Option[String] = None): List[(Node[?], NodeCheck)] = w.check(only).unsafeRunSync()._1
    def analysis: Analysis = w.analysis.unsafeRunSync()
    def generate: Generate = analysis.generate
    def baseSnapshot: Snapshot = analysis.snapshot
    def scaffold(n: Node[?]): Boolean = w.analysis.flatMap(Scaffold(_, w.lake, n)).unsafeRunSync().isDefined

  protected def workflow(kb: KnowledgeBase): Lab =
    assume(lakeAvailable, "lake is not available")
    LeanLab.kernelBuilt
    Lab(OnDisk(kb, Workspace(tempDir("frflow"), kernel.toString)).unsafeRunSync())

  protected def statuses(r: List[(Node[?], NodeCheck)]) = r.map((n, c) => n.id -> c.status.toString)
  protected def of(r: List[(Node[?], NodeCheck)], id: String) = r.find(_._1.id == id).get._2
  protected def result(c: NodeCheck, name: String) = c.obligations.find(_.name.lean == name)
  protected def node(w: Lab, id: String) = w.baseSnapshot.nodes.find(_.id == NodeId(id)).get
  protected def splitOf(w: Lab, n: Node[?]) = node(w, n.id).split.get
  protected def st(split: Split, k: String) = Some((if k == "clash" then split.clash else split.complete).status.toString)

object LeanLab:
  val Lean = new munit.Tag("Lean")

  lazy val kernel: Path =
    Iterator.iterate(Paths.get(sys.props("user.dir")).toAbsolutePath)(_.getParent).takeWhile(_ != null)
      .map(_.resolve("lean")).find(p => Files.exists(p.resolve("FrFlow.lean"))).getOrElse(sys.error("kernel not found"))

  lazy val available: Boolean = Config.load.flatMap(Lake(Paths.get("."), _)).flatMap(_.available).unsafeRunSync()

  /** The kernel built once, before any workspace that requires it builds: suites run in parallel, and two Lake builds
    * of the same package at once would race on its build directory.
    */
  lazy val kernelBuilt: Unit =
    val run = Config.load.flatMap(Lake(kernel, _)).flatMap(_.build("FrFlow")).unsafeRunSync()
    assert(run.ok, run.output)

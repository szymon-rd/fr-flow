package frflow
package check

import java.nio.file.Path
import java.util.concurrent.TimeUnit

final case class Run(exitCode: Int, output: String):
  def ok: Boolean = exitCode == 0

/** Runs `lake` in a Lean workspace. The executable is `FRFLOW_LAKE`, or `lake` on the PATH. */
final class Lake(dir: Path, timeoutSeconds: Long = 900):
  private val lake = sys.env.getOrElse("FRFLOW_LAKE", "lake")

  // Builds write the workspace's build outputs: one at a time. Elaborating and replaying only read them.
  def build(target: String): Run = Lake.building.synchronized(run(Seq(lake, "build", target)))
  /** Several targets in one build: Lake builds them in parallel. */
  def buildAll(targets: Seq[String]): Run = Lake.building.synchronized(run(Seq(lake, "build") ++ targets))
  def elaborate(file: String): Run = run(Seq(lake, "env", "lean", file))
  def available: Boolean =
    try ProcessBuilder(lake, "--version").redirectErrorStream(true).start().waitFor() == 0
    catch case _: java.io.IOException => false

  private def run(cmd: Seq[String]): Run =
    val t0 = System.nanoTime
    val r = runTimed(cmd)
    // FRFLOW_TIMING=1: each Lean run, with how long it took (to see where a check spends its time).
    if sys.env.contains("FRFLOW_TIMING") then System.err.println(f"[lean ${(System.nanoTime - t0) / 1e9}%.1fs] ${cmd.drop(1).mkString(" ").take(140)}")
    r

  private def runTimed(cmd: Seq[String]): Run =
    val proc = ProcessBuilder(cmd*).directory(dir.toFile).redirectErrorStream(true).start()
    val out = java.io.ByteArrayOutputStream()
    val pump = Thread(() => { proc.getInputStream.transferTo(out); () })
    pump.start()
    if !proc.waitFor(timeoutSeconds, TimeUnit.SECONDS) then
      proc.destroyForcibly()
      pump.join(1000)
      Run(124, out.toString("UTF-8") + s"\ntimed out after ${timeoutSeconds}s")
    else
      pump.join()
      Run(proc.exitValue(), out.toString("UTF-8"))

object Lake:
  private val building = Object()

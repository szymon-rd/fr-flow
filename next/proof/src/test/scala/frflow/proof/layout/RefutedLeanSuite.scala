package frflow.proof.layout

import frflow.proof.lean.print.Print
import java.nio.file.Files

/** The refutation built by Lean: Lean proves `complete` false on the case. */
class RefutedLeanSuite extends munit.FunSuite:
  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(20, "minutes")
  test("refuted: Lean proves the step false on the case".tag(LeanTag)) {
    val out = LeanWorkspace.use("refuted")(_.build(Refuted.modules)._2)
    val refutes = Refuted.modules.last
    val e = frflow.proof.reading.Elaboration(Print.module(refutes), out, refutes.name.file.value.stripPrefix("lean/"))
    assert(out.linesIterator.exists(l => l.contains(s" ${refutes.name.dotted} ") && !l.startsWith("✖")), out)
    assertEquals(e.verdict("refutes"), frflow.proof.reading.TheoremVerdict.Proven, out)
  }

  test("a workspace is deleted once its use is done, and kept only when asked (FRFLOW_KEEP_LEAN)") {
    val gone = LeanWorkspace.use("gone", keep = false)(w => { w.write("A.lean", "-- a"); w.dir })
    val kept = LeanWorkspace.use("kept", keep = true)(_.dir)
    assert(!Files.exists(gone) && Files.exists(kept.resolve("lakefile.toml")))
    Files.walk(kept).sorted(java.util.Comparator.reverseOrder()).forEach(p => Files.delete(p))
  }

package frflow.proof.layout

import frflow.proof.lean.print.Print

/** The refutation built by Lean: Lean proves `complete` false on the case. */
class RefutedLeanSuite extends munit.FunSuite:
  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(20, "minutes")
  test("refuted: Lean proves the step false on the case".tag(LeanTag)) {
    val out = LeanWorkspace.make("refuted").build(Refuted.modules)._2
    val refutes = Refuted.modules.last
    val e = frflow.proof.reading.Elaboration(Print.module(refutes), out, refutes.name.file.value.stripPrefix("lean/"))
    assert(out.linesIterator.exists(l => l.contains(s" ${refutes.name.dotted} ") && !l.startsWith("✖")), out)
    assertEquals(e.verdict("refutes"), frflow.proof.reading.TheoremVerdict.Proven, out)
  }

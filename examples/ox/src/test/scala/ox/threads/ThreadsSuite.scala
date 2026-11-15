package ox.threads

import frflow.project.{Live, Ported, Projects}
import java.nio.file.{Files, Paths}
import scala.annotation.experimental
import scala.concurrent.duration.*

/** The model of Ox's threads: FrFlow generates its Rocq, and each step from parts to a claim is proven by hand in
  * the claim's proof file (`examples/ox/rocq/Proofs/OxThreads`).
  */
@experimental class ThreadsSuite extends munit.CatsEffectSuite:
  override val munitIOTimeout: Duration = 60.minutes

  test("the model elaborates, its calls named as Ox's code names them") {
    val files = Projects.bare(Projects.elaborated(oxThreads)).rocq.files
    files.foreach { (file, text) =>
      val p = Paths.get("examples/ox/target/generated/threads").resolve(file.toString)
      Files.createDirectories(p.getParent)
      Files.writeString(p, text)
    }
    val text = files.map(_._2).mkString("\n")
    assert(text.contains("\"ox.internal.ThreadHerd startThread scala.Function0:scala.Unit\""), "startThread")
    assert(text.contains("(heldIn \"ox.internal.ThreadHerd threads\"%string h)"), "threads")
  }

  test("every step of the model is proven, and what it states at the bottom can hold together".tag(Live)) {
    Ported.run(Projects.elaborated(oxThreads), Nil, Ported.proofs("ox", "OxThreads")).map(r =>
      assertEquals(Ported.unproven(r), Map.empty, Ported.table(r)))
  }

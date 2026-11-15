package frflow.executions.latch

import frflow.project.{Live, Ported, Projects}
import java.nio.file.{Files, Paths}
import scala.concurrent.duration.*

/** A claim of code read from its TASTy, proven of its tree: `Latch.enter` returns only if it read the flag unset.
  * The plain test writes the generated Rocq under `target/generated/latch`.
  */
class LatchSuite extends munit.CatsEffectSuite:
  override val munitIOTimeout: Duration = 30.minutes

  private val proofs = List("enterReadsItOpen", "enterFindsItOpen", "Whole").map(n =>
    n -> Ported.resource(s"latch/$n.v"))

  private lazy val files = Projects.bare(Projects.elaborated(latch)).rocq.files

  test("the code read is a module of trees, and every statement about the execution takes it as one of the code") {
    val out = Paths.get("modules/executions/target/generated/latch")
    files.foreach { (f, text) =>
      val to = out.resolve(f.toString); Files.createDirectories(to.getParent); Files.writeString(to, text) }
    val texts = files.map((f, t) => f.toString -> t).toMap
    assert(texts.keys.exists(_.endsWith("Latch/Code/frflow_executions_latch_Latch.v")), texts.keys)
    assert(texts.find(_._1.endsWith("Latch/Code.v")).exists(_._2.contains("Definition Code_runs")), texts.keys)
    val spec = texts.find(_._1.endsWith("enterReadsItOpen/Spec.v")).map(_._2).getOrElse(fail("no spec"))
    assert(spec.contains("(o_history_0 : (Code_runs history))"), spec)
  }

  test("`enter` returns only if the flag was unset: proven of the tree read and of what is assumed".tag(Live)) {
    Ported.run(Projects.elaborated(latch), Nil, proofs).map(r =>
      assertEquals(Ported.unproven(r), Map.empty, Ported.table(r)))
  }

  test("a claim of the code with no part is asked of every execution of the code, alone") {
    val texts = Projects.bare(Projects.elaborated(latchUnproven)).rocq.files.map((f, t) => f.toString -> t).toMap
    val spec = texts.find(_._1.endsWith("enterReadsItOpen/Spec.v")).map(_._2).getOrElse(fail("no spec"))
    assert(spec.contains("Definition enterReadsItOpen_Obl_complete : Prop :=\n" +
      "  forall (heldIn : string -> Value -> Value), forall (history : Z -> Event), " +
      "forall (o_history_0 : (Code_runs history)), (enterReadsItOpen_claim heldIn history)."), spec)
  }

  test("with no proof it stands unproven, and so does what is proven from it".tag(Live)) {
    Ported.run(Projects.elaborated(latchUnproven), Nil, Nil).map { r =>
      assert(Ported.unproven(r).getOrElse("enterReadsItOpen", Nil).contains("OfCode"), Ported.table(r))
      assertEquals(Ported.standsOn(r).get("enterFindsItOpen").map(_._1.contains("enterReadsItOpen")), Some(true))
    }
  }

package frflow.executions.sets

import frflow.project.{Live, Ported, Projects}
import scala.concurrent.duration.*

/** A model over a run with no code: a concurrent set as its assumptions say it. FrFlow generates its Rocq as it does
  * any model's, and the step from the assumptions to the claim is proven by hand in the claim's proof file.
  */
class SetsSuite extends munit.CatsEffectSuite:
  override val munitIOTimeout: Duration = 30.minutes

  private val proofs = List("Lemmas", "whoIsAddedStays", "Whole").map(n => n -> Ported.resource(s"sets/$n.v"))

  test("a model over a run elaborates: the run and the set's elements are what its statements are about") {
    val a = Projects.bare(Projects.elaborated(sets))
    val claim = a.rocq.files.collectFirst { case (f, t) if f.toString.endsWith("whoIsAddedStays/Spec.v") => t }
    assert(claim.exists(_.contains(
      "Definition whoIsAddedStays_claim (elements : Value -> Z -> (Value -> Prop)) (history : Z -> Event) : Prop")))
  }

  test("what is added to a set and not removed is in it: proven from the set's assumptions".tag(Live)) {
    Ported.run(Projects.elaborated(sets), Nil, proofs).map(r =>
      assertEquals(Ported.unproven(r), Map.empty, Ported.table(r)))
  }

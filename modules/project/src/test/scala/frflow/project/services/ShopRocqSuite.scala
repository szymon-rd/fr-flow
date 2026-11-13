package frflow.project.services

import frflow.eval.run.OnCode
import frflow.project.{Live, Ported, Projects}
import shop.ShopExamples
import scala.annotation.experimental
import scala.concurrent.duration.*

/** The shop (`examples/shop`), checked by Rocq end to end: the class given for each store, each service over a
  * store and the checkout over the services is proven to meet the claims on it, the checkout's from the claims on
  * what it holds; its examples hold on the code. The claims do not decide the examples in Rocq yet (`docs/ROCQ.md`).
  */
@experimental class ShopRocqSuite extends munit.CatsEffectSuite:
  override val munitIOTimeout: Duration = 60.minutes

  test("every claim of the shop is proven, and its examples hold on the code".tag(Live)) {
    val examples = ShopExamples().elaborated.fold(e => throw AssertionError(e.toString), identity)
    Ported.run(Projects.elaborated(shop.shop), examples, Ported.proofs("shop", "Shop")).map { r =>
      assertEquals(Ported.unproven(r), Map.empty, Ported.table(r))
      assertEquals(r.computed.examples.map(_._2).distinct, List(OnCode.Holds))
    }
  }

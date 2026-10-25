package frflow
package flow

/** A program attached to a contract as its proven code: a `def` from its input to a flow. */
final class FlowDef[A, R] @scala.annotation.publicInBinary private[frflow] (val name: String, f: Term[A] => Flow[R],
    inType: LeanType[A], val source: String):
  private[frflow] lazy val built: (Binder, Steps, LeanType[?]) =
    Building {
      val b = Lambda.binders(f, List(inType)).head
      val (s, t) = Steps.of(f(b.term))
      (b, s, t)
    }

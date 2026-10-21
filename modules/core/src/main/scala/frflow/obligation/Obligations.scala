package frflow.obligation

import frflow.model.*

enum ObligationKind:
  /** Initial states establish an invariant. */
  case InitInvariant
  /** An event preserves an invariant. */
  case EventInvariant
  /** Initial states map to abstract initial states. */
  case InitAbs
  /** Guard strengthening: the concrete guard implies the abstract guard. */
  case Guard
  /** Action simulation: the concrete action maps to the abstract action. */
  case Simulation
  /** A new event leaves the abstract state unchanged. */
  case Skip

/** One proof obligation. `statement` is the Lean proposition; it is rendered as
  * `def <name> : Prop := <statement>` in the node's `Obl` namespace and must be
  * proven by `theorem <name> : Obl.<name>` in the node's proof file.
  */
final case class Obligation(
    name: String,
    kind: ObligationKind,
    event: Option[String],
    invariant: Option[String],
    statement: String,
    description: String
)

/** An invariant as it enters obligation generation. The gluing invariant of the
  * link is treated as an invariant named `glue`.
  */
final case class EffectiveInvariant(name: String, leanRef: String, fromLink: Boolean)

object Obligations:

  val GlueName = "glue"

  def effectiveInvariants(node: Node): Seq[EffectiveInvariant] =
    val glue = node.link.flatMap(_.glue).map(_ => EffectiveInvariant(GlueName, GlueName, fromLink = true))
    glue.toSeq ++ node.spec.invariants.map(i => EffectiveInvariant(i.name, i.name, fromLink = false))

  /** All obligations of a node, in a stable order. */
  def forNode(theory: TheoryModel, node: Node): Seq[Obligation] =
    val invs = effectiveInvariants(node)
    val parentNs = theory.parentOf(node).map(_.id)

    val initInvs = invs.map { i =>
      Obligation(
        name = s"init_${i.name}",
        kind = ObligationKind.InitInvariant,
        event = None,
        invariant = Some(i.name),
        statement = s"∀ s, Init s → ${i.leanRef} s",
        description = s"Every initial state of ${node.id} satisfies ${i.name}."
      )
    }

    val initAbs = parentNs.toSeq.map { p =>
      Obligation(
        name = "init_abs",
        kind = ObligationKind.InitAbs,
        event = None,
        invariant = None,
        statement = s"∀ s, Init s → $p.Init (abs s)",
        description = s"Every initial state of ${node.id} maps to an initial state of $p."
      )
    }

    val perEvent = node.spec.events.flatMap { e =>
      val ev = e.name
      val hyp = s"∀ s p, Obl.Hyp s → $ev.guard s p →"
      val invObls = invs.map { i =>
        Obligation(
          name = s"${ev}_inv_${i.name}",
          kind = ObligationKind.EventInvariant,
          event = Some(ev),
          invariant = Some(i.name),
          statement = s"$hyp ${i.leanRef} ($ev.act s p)",
          description = s"Event $ev preserves ${i.name}."
        )
      }
      val linkObls = (parentNs, e.target) match
        case (Some(p), EventTarget.Refines(ae, _)) =>
          Seq(
            Obligation(
              name = s"${ev}_grd",
              kind = ObligationKind.Guard,
              event = Some(ev),
              invariant = None,
              statement = s"$hyp $p.$ae.guard (abs s) ($ev.witness s p)",
              description = s"Whenever $ev is enabled in ${node.id}, $p.$ae is enabled for the witness parameters."
            ),
            Obligation(
              name = s"${ev}_sim",
              kind = ObligationKind.Simulation,
              event = Some(ev),
              invariant = None,
              statement = s"$hyp abs ($ev.act s p) = $p.$ae.act (abs s) ($ev.witness s p)",
              description = s"The effect of $ev, seen through abs, is the effect of $p.$ae."
            )
          )
        case (Some(p), EventTarget.Skip) =>
          Seq(
            Obligation(
              name = s"${ev}_skip",
              kind = ObligationKind.Skip,
              event = Some(ev),
              invariant = None,
              statement = s"$hyp abs ($ev.act s p) = abs s",
              description = s"Event $ev does not change the state of $p (it refines skip)."
            )
          )
        case _ => Nil
      invObls ++ linkObls
    }

    initInvs ++ initAbs ++ perEvent

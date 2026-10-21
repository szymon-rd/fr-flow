package frflow.obligation

import frflow.model.*
import frflow.render.LeanPrinter

enum ObligationKind:
  /** A law of the theory. */
  case Law
  /** Initial states establish an invariant. */
  case InitInvariant
  /** An operation preserves an invariant. */
  case OpInvariant
  /** Initial states map to initial states of the parent. */
  case InitAbs
  /** Guard strengthening: the guard implies the parent operation's guard. */
  case Guard
  /** Simulation: the effect, seen through the abstraction, is the parent operation's effect. */
  case Simulation
  /** A new operation leaves the parent state unchanged. */
  case Skip

/** One proof obligation. `statement` is a Lean proposition, rendered as
  * `def <name> : Prop := <statement>` in the node's `Obl` namespace. It is proven
  * by `frflow_auto` in the generated `Auto` module, or by an authored
  * `theorem <name> : Obl.<name>` in the node's proof file.
  */
final case class Obligation(
    name: String,
    kind: ObligationKind,
    operation: Option[String],
    invariant: Option[String],
    statement: String,
    description: String
)

/** An invariant as it enters obligation generation. The gluing invariant of the
  * link is the invariant named `glue`.
  */
final case class EffectiveInvariant(name: String, fromLink: Boolean)

object Obligations:

  val GlueName = "glue"

  def effectiveInvariants(l: LayerModel): List[EffectiveInvariant] =
    l.link.flatMap(_.glue).map(_ => EffectiveInvariant(GlueName, fromLink = true)).toList ++
      l.invariants.map(i => EffectiveInvariant(i.name, fromLink = false))

  /** Obligations of the theory: one per law. */
  def forTheory(m: TheoryModel): List[Obligation] =
    m.laws.map { law =>
      val body = LeanPrinter.expr(law.lifted.body)
      val stmt = if law.lifted.params.isEmpty then body else s"∀ ${LeanPrinter.binders(law.lifted.params)}, $body"
      Obligation(law.name, ObligationKind.Law, None, None, stmt, law.statement)
    }

  /** All obligations of a layer, in a stable order. */
  def forLayer(m: TheoryModel, l: LayerModel): List[Obligation] =
    val invs = effectiveInvariants(l)
    val parent = m.parentOf(l).map(_.id)

    val initInvs = invs.map { i =>
      Obligation(s"init_${i.name}", ObligationKind.InitInvariant, None, Some(i.name),
        s"∀ s, Init s → ${i.name} s", s"Every initial state of ${l.id} satisfies ${i.name}.")
    }
    val initAbs = parent.toList.map { p =>
      Obligation("init_abs", ObligationKind.InitAbs, None, None,
        s"∀ s, Init s → $p.Init (abs s)", s"Every initial state of ${l.id} maps to an initial state of $p.")
    }
    val perOp = l.ops.flatMap { op =>
      val o = op.name
      val hyp = s"∀ s p, Obl.Hyp s → $o.guard s p →"
      val invObls = invs.map { i =>
        Obligation(s"${o}_inv_${i.name}", ObligationKind.OpInvariant, Some(o), Some(i.name),
          s"$hyp ${i.name} ($o.act s p)", s"Operation $o preserves ${i.name}.")
      }
      val linkObls = (parent, op.target) match
        case (Some(p), TargetModel.Refines(_, ao, _)) =>
          List(
            Obligation(s"${o}_grd", ObligationKind.Guard, Some(o), None,
              s"$hyp $p.$ao.guard (abs s) ($o.witness s p)",
              s"Whenever $o is enabled in ${l.id}, $p.$ao is enabled for the witness parameters."),
            Obligation(s"${o}_sim", ObligationKind.Simulation, Some(o), None,
              s"$hyp abs ($o.act s p) = $p.$ao.act (abs s) ($o.witness s p)",
              s"The effect of $o, seen through abs, is the effect of $p.$ao.")
          )
        case (Some(p), TargetModel.Skip) =>
          List(
            Obligation(s"${o}_skip", ObligationKind.Skip, Some(o), None,
              s"$hyp abs ($o.act s p) = abs s", s"Operation $o does not change the state of $p (it refines skip).")
          )
        case _ => Nil
      invObls ++ linkObls
    }
    initInvs ++ initAbs ++ perOp

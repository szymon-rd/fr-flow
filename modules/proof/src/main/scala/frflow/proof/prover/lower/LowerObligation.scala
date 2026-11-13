package frflow.proof.prover.lower

import frflow.core.name.ProverNames
import frflow.proof.prover.ast.*
import frflow.proof.prover.lower.Atoms
import frflow.proof.obligation.{Obligation, ObligationName, TryKind}

/** An obligation as a node's `Spec` declares it: in `namespace Obl`, documented, `@[frflow_defs] def name : Prop`. */
final class LowerObligation(props: LowerProp):
  def apply(o: Obligation): Decl =
    val statement = props.statement(o.goal)
    val decl = Decl.Def(List(Attr.FrflowDefs), LowerObligation.name(o.name), Nil, Atoms.name("Prop"), statement)
    Decl.Namespace(Names.path("Obl"), List(Decl.Documented(o.doc, decl)))

object LowerObligation:
  /** The theorem's name: `complete`, `needed_GrantLetsIn`, `restates_2_Visibility`, `eval_0`. */
  def name(o: ObligationName): ProverName = Names.builtin(o match
    case ObligationName.Complete      => "complete"
    case ObligationName.Feasible      => "feasible"
    case ObligationName.Outside       => "outside"
    case ObligationName.Impl          => "impl"
    case ObligationName.RootImpl      => "root_impl"
    case ObligationName.Made(m)       => ProverNames.Made + m
    case ObligationName.Consistent(i) => s"consistent_$i"
    case ObligationName.Inhabited(n)  => s"inhabited_${n.value}"
    case ObligationName.Satisfiable(n, i) => s"satisfiable_${i + 1}_${n.value}"
    case ObligationName.Example(of, i) => s"example_${of}_$i"
    case ObligationName.ExampleOpposite(of, i) => s"example_${of}_${i}_opposite"
    case ObligationName.Tried(kind)   => tried(kind))

  private def tried(k: TryKind): String = k match
    case TryKind.Needed(c)              => s"needed_${c.value}"
    case TryKind.Vacuous                => "vacuous"
    case TryKind.Restates               => "restates"
    case TryKind.Clash                  => "clash"
    case TryKind.Unsat                  => "unsat"
    case TryKind.Idle                   => "idle"
    case TryKind.RestatesConjunct(p, i) => s"restates_${i}_${p.value}"

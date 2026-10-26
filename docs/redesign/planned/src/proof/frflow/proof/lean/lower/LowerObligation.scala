package frflow.proof.lean.lower

import frflow.proof.lean.ast.*
import frflow.proof.lean.lower.Atoms
import frflow.proof.obligation.{Obligation, ObligationName, TryKind}

/** An obligation as a node's `Spec` declares it: in `namespace Obl`, documented, `@[frflow_defs] def name : Prop`. */
final class LowerObligation(props: LowerProp):
  def apply(o: Obligation): Decl =
    val statement = props.statement(o.goal)
    val decl = Decl.Def(List(Attr.FrflowDefs), LowerObligation.name(o.name), Nil, Atoms.name("Prop"), statement)
    Decl.Namespace(Names.path("Obl"), List(Decl.Documented(o.doc, decl)))

object LowerObligation:
  /** The theorem's name: `complete`, `needed_GrantLetsIn`, `restates_2_Visibility`, `eval_0`. */
  def name(o: ObligationName): LeanName = Names.builtin(o match
    case ObligationName.Complete      => "complete"
    case ObligationName.Feasible      => "feasible"
    case ObligationName.Impl          => "impl"
    case ObligationName.Check         => "check"
    case ObligationName.RootImpl      => "root_impl"
    case ObligationName.Cover(i)      => s"cover_$i"
    case ObligationName.Expect(i)     => s"expect_$i"
    case ObligationName.Eval(i)       => s"eval_$i"
    case ObligationName.EvalImpl(i)   => s"eval_impl_$i"
    case ObligationName.Probe(j)      => s"probe_$j"
    case ObligationName.ProbeImpl(j)  => s"probe_impl_$j"
    case ObligationName.Commute(i)    => s"commute_$i"
    case ObligationName.Tried(kind)   => tried(kind))

  private def tried(k: TryKind): String = k match
    case TryKind.Needed(c)              => s"needed_${c.value}"
    case TryKind.Vacuous                => "vacuous"
    case TryKind.Restates               => "restates"
    case TryKind.Clash                  => "clash"
    case TryKind.Unsat                  => "unsat"
    case TryKind.Idle                   => "idle"
    case TryKind.VacuousExpect(i)       => s"vacuous_expect_$i"
    case TryKind.RestatesConjunct(p, i) => s"restates_${i}_${p.value}"

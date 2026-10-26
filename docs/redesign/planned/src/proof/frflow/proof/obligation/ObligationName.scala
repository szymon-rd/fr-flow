package frflow.proof.obligation

import cats.Order

/** What Lean is asked about a node: the name of its theorem (`lean.lower.LowerObligation.name` spells it). */
enum ObligationName:
  case Complete, Feasible, Impl, Check, RootImpl
  case Cover(invariant: String)
  case Expect(i: Int)
  case Tried(kind: TryKind)
  case Eval(i: Int)
  case EvalImpl(i: Int)
  case Probe(j: Int)
  case ProbeImpl(j: Int)
  case Commute(i: Int)

object ObligationName:
  given Order[ObligationName] = Order.by(_.toString)

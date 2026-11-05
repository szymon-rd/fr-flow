package frflow.core.consistency

import frflow.core.name.{NodeId, SymbolName}

/** How an open value of a group gets a meaning under which the group's statements hold (owner §15, §18). */
enum Witness:
  /** `∀ xs, s(xs) = e` in a statement of the group, `e` mentioning nothing open: `fun xs => e`, of which the
    * statement holds by `rfl` (`granted(held, request) === held.forall(b => noOverlap(b, request))`; auth's
    * `authorized(u, p) === grants.contains(Grant(u, p))`).
    */
  case Equation(symbol: SymbolName, from: NodeId, picked: Picked)
  /** `∀ xs, s(xs) ≤ e` (or `<`, `≥`, `>`): the bound itself, or one past a strict one. */
  case Bound(symbol: SymbolName, from: NodeId, picked: Picked)
  /** None derived, and plain Scala defines it, tested: evidence that a meaning exists, not proof. */
  case Tested(symbol: SymbolName)
  /** None derived: the developer proves the group consistent, or it shows "consistency not proven". */
  case Missing(symbol: SymbolName)
  /** A list provided where the code runs that no premise equates or bounds: the empty list, which a premise about
    * each of its elements meets (keycloak's `freshTokens` of `history`).
    */
  case Empty(symbol: SymbolName)

  def meaningOf: SymbolName = this match
    case Equation(s, _, _) => s
    case Bound(s, _, _)    => s
    case Tested(s)         => s
    case Missing(s)        => s
    case Empty(s)          => s

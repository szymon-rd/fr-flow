package frflow
package term

/** What holds always, as a whole claim: `Node.claim("…")(always[Booking](b => b.start < b.end))`, every value of a
  * type that can be made; `Node.claim("…")(always(stored)(held => held.pairwise(apart)))`, every state a store
  * reaches. Unlike `forall` (every possible value, proven), it holds where FrFlow covers the code: it is a hypothesis
  * of every statement about such values, tests draw only values that hold it, and every program using the store
  * keeps it.
  */
final class Always private[frflow] (val store: Option[StateModel[?]], tree: Tree)
    extends Term[Boolean](tree, summon[LeanType[Boolean]]):
  /** The rule's variable and body. */
  private[frflow] def rule: (Binder, Tree) = tree match
    case Tree.Quant(true, List(b), body) => (b, body)
    case other                           => throw IllegalStateException(s"FrFlow: always over one variable, not $other")

object Always:
  /** Every value of `T` that can be made holds `rule`. */
  def always[T](rule: Term[T] => Term[Boolean])(using t: LeanType[T]): Term[Boolean] =
    Always(None, Term.quant(all = true, rule, List(t)).termTree)
  /** Every state the store's model reaches holds `rule`. */
  def always[S](store: StateModel[S])(rule: Term[S] => Term[Boolean]): Term[Boolean] =
    Always(Some(store), Term.quant(all = true, rule, List(store.stateType)).termTree)

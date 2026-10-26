package frflow
package node

/** What an `always` claim says always holds: `rule`, a `define` named as the claim's val, of every value of its type
  * that can be made, or (`store`) of every state the store's model reaches.
  */
final case class AlwaysRule(rule: Def[?], store: Option[StateModel[?]])

object AlwaysRule:
  private[frflow] def of(name: String, a: frflow.term.Always, source: String): AlwaysRule =
    val (b, body) = a.rule
    val bool = summon[LeanType[Boolean]]
    AlwaysRule(Def(Lifted(() => (List(b), Term(body, bool)), null, source), bool, Some(name)), a.store)

package frflow
package check

import frflow.protocol.{NodeKind as _, *}
import frflow.protocol.ObligationStatus.*

/** How a node's parts make it (docs/DAG.md §4): `complete`, each part `needed`, and `clash`, each with a
  * status and a detail. `complete`: `proven`, `open`, `failed`; each part: `needed` or `not-needed`;
  * `clash`: `no-clash` or `clash`; any of them `unchecked`, `timeout` or `informal` when not checked. None
  * for a node with no parts. `needed` and `no-clash` are tries that found no proof: nothing is shown wrong,
  * nothing is proven.
  */
object Splits:
  def of(a: Analysis, n: Node[?]): Option[Split] =
    val parts = a.kb.parts(n)
    def all(o: Outcome) = Split(o, parts.map(p => Split.Part(NodeId(p.id), o.status, o.detail)), o)
    if parts.isEmpty || !a.kb.isStatement(n) then None
    else if a.generate.splitParts(n).isEmpty then Some(all(Outcome(Informal, "not formalized: decided by reading")))
    else Some(a.current(n).fold(all(notCurrent(a.checks.get(NodeId(n.id)))))(checked(parts, _)))

  /** No current check: why, from the last one. */
  private def notCurrent(c: Option[NodeCheck]): Outcome =
    val why = c.filter(_.status == CheckStatus.Waiting).flatMap(_.messages.headOption)
      .orElse(c.filter(_.status == CheckStatus.Timeout).map(_ => "Lean timed out: run check again"))
      .getOrElse(if c.isDefined then "changed since the last check" else "not checked yet")
    c.map(_.status) match
      case Some(CheckStatus.Timeout) => Outcome(Timeout, why)
      case Some(CheckStatus.ModelError) => Outcome(Failed, "the model does not build: " + c.flatMap(_.messages.headOption).getOrElse(""))
      case _ => Outcome(Unchecked, why)

  private def checked(parts: List[Node[?]], c: NodeCheck): Split =
    val complete = c.result("complete") match
      case Some(r) if r.status == Proven && c.obligations.exists(o => o.name == "feasible" && o.status != Proven) =>
        Outcome(Open, "its parts make it by an authored proof: prove `feasible` too (some world meets the parts), or give a proven implementation below")
      case Some(r) => Outcome(r.status, r.detail.linesIterator.nextOption().getOrElse(""))
      case None => Outcome(Failed, c.messages.headOption.getOrElse("the check failed"))
    val needed = parts.map(p => c.result(if parts.size == 1 then "vacuous" else s"needed_${p.id}")
      .fold(Split.Part(NodeId(p.id), Unchecked, "not checked"))(r => Split.Part(NodeId(p.id), r.status, r.detail)))
    Split(complete, needed, c.result("clash").fold(Outcome(Unchecked, "not checked"))(Outcome.of))

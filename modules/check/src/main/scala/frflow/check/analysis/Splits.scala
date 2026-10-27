package frflow
package check
package analysis

import frflow.protocol.*
import frflow.protocol.ObligationName.{Complete, Feasible, Tried}
import frflow.protocol.ObligationStatus.*

/** How a node's parts make it (docs/DAG.md §4): `complete`, each part `needed`, and `clash`; none for a node with no parts. */
object Splits:
  def of(a: Analysis, n: Node[?]): Option[Split] =
    val (rules, parts) = a.kb.parts(n).partition(frflow.lean.Refinement.isRule)
    def all(o: Outcome) =
      Split(o, parts.map(p => Split.Part(NodeId(p.id), o.status, o.detail)) ++ rules.map(ruled(a, n, _)), o)
    if parts.isEmpty || !a.kb.isStatement(n) || n.isAlways then None
    else Some(a.current(n).fold(all(notCurrent(a.checks.get(NodeId(n.id)))))(c =>
      val s = checked(parts, c)
      s.copy(needed = s.needed ++ rules.map(ruled(a, n, _)))))

  /** An `always` claim among the parts is not a hypothesis of the step (it says nothing Lean proves of a value): it is
    * needed exactly when the node's statement takes what it says, of what the node quantifies over.
    */
  private def ruled(a: Analysis, n: Node[?], r: Node[?]): Split.Part =
    if a.kb.invariantsUsedBy(n).exists(_ eq r) then
      Split.Part(NodeId(r.id), NotShown, s"what it says always holds is a hypothesis of ${n.id}, of what it is about")
    else Split.Part(NodeId(r.id), Shown, s"${n.id} is about nothing ${r.id} says always holds")

  private def notCurrent(c: Option[NodeCheck]): Outcome =
    val why = c.filter(_.status == CheckStatus.Waiting).flatMap(_.messages.headOption)
      .orElse(c.filter(_.status == CheckStatus.Timeout).map(_ => "Lean timed out: run check again"))
      .getOrElse(if c.isDefined then "changed since the last check" else "not checked yet")
    c.map(_.status) match
      case Some(CheckStatus.Timeout) => Outcome(Timeout, why)
      case Some(CheckStatus.ModelError) => Outcome(Failed, "the model does not build: " + c.flatMap(_.messages.headOption).getOrElse(""))
      case _ => Outcome(Unchecked, why)

  private def checked(parts: List[Node[?]], c: NodeCheck): Split =
    val complete = c.result(Complete) match
      case Some(r) if r.status == Proven && c.obligations.exists(o => o.name == Feasible && o.status != Proven) =>
        Outcome(Open, "its parts make it by an authored proof: prove `feasible` too (some world meets the parts), or give a proven implementation below")
      case Some(r) => Outcome(r.status, r.detail.linesIterator.nextOption().getOrElse(""))
      case None => Outcome(Failed, c.messages.headOption.getOrElse("the check failed"))
    val needed = parts.map(p => c.result(Tried(if parts.size == 1 then TryKind.Vacuous else TryKind.Needed(p.id)))
      .fold(Split.Part(NodeId(p.id), Unchecked, "not checked"))(r => Split.Part(NodeId(p.id), r.status, r.detail)))
    Split(complete, needed, c.result(Tried(TryKind.Clash)).fold(Outcome(Unchecked, "not checked"))(Outcome.of))

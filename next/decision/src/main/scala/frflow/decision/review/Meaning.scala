package frflow.decision.review

import frflow.decision.content.{Chain, Content, Hash, Sha}
import frflow.decision.ledger.Decision

/** What a node's content means apart from its wording: what a decision binds, and what moves the nodes below. */
object Meaning:
  private val meaningful = Set("statement", "sources", "substitutions", "vocabulary", "uses", "governs", "op")

  /** Its content without its place, cause `self`; a design keeps its parents, since placing it is what is decided
    * (its chain is empty: docs/DAG.md §5).
    */
  def own(c: Content): Content = c.without(if c.text("kind") == "design" then Set("parts") else Set("parts", "parents"))

  /** Without its reason, examples or parents' names. */
  def of(c: Content): Hash = c.only(meaningful).hash

  /** What a formal node means to Lean: its meaning without the words of its statement. */
  def formal(c: Content): Hash = of(c.without(_ == "statement"))

  /** What it says moved since `d` was taken, by today's rule: its own content with the premises it assumes, its
    * implementation left out once Lean proves it (no `Implementation` or `RootImpl` open). Examples are not content.
    */
  def decisionMoved(d: Decision, s: Subject): Boolean =
    val proven = !s.proof.unproven.exists(u => u == Unproven.Implementation || u == Unproven.RootImpl)
    def decided(c: Content): Hash = own(c).without(k => proven && k == "implementation").hash
    decided(d.bound.content) != decided(s.content)

  def chain(meaning: Hash, above: Chain): Chain = Chain(Sha.parts(meaning.value, above.value))

  /** The chain over several nodes rested on: their chains, sorted, hashed together. */
  def over(chains: List[Chain]): Chain =
    if chains.isEmpty then Chain.empty
    else Chain(Sha.parts((Chain.empty :: chains.sortBy(_.value)).map(_.value)*))

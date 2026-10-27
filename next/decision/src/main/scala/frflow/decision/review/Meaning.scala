package frflow.decision.review

import frflow.decision.content.{Chain, Content, Hash, Sha}
import frflow.decision.ledger.Decision

/** What a node's content means apart from its wording: what a decision binds, and what moves the nodes below. */
object Meaning:
  private val meaningful = Set("statement", "formula", "vocabulary", "governs", "call", "failure", "model")

  /** What is shown and not decided: a formula as the Scala wrote it (its meaning is `formula`). */
  private val shown = Set("written")

  /** Its content without its place, cause `self`, or what is only shown; a design keeps its parents, since placing
    * it is what is decided (its chain is empty: docs/DAG.md §5).
    */
  def own(c: Content): Content =
    c.without(shown ++ (if c.text("kind") == "design" then Set("parts") else Set("parts", "parents")))

  /** Without its reason, examples or parents' names. */
  def of(c: Content): Hash = c.only(meaningful).hash

  /** What a formal node means to Lean: its meaning without the words of its statement. */
  def formal(c: Content): Hash = of(c.without(_ == "statement"))

  /** What it says moved since `d` was taken, by today's rule: its own content with the premises it assumes, its
    * implementation left out once Lean proves its code (tested code stays in). Examples are not content.
    */
  def decisionMoved(d: Decision, s: Subject): Boolean =
    def decided(c: Content): Hash = own(c).without(k => s.proof.codeProven && k == "implementation").hash
    decided(d.bound.content) != decided(s.content)

  def chain(meaning: Hash, above: Chain): Chain = Chain(Sha.parts(meaning.value, above.value))

  /** The chain over several nodes rested on: their chains, sorted, hashed together. */
  def over(chains: List[Chain]): Chain =
    if chains.isEmpty then Chain.empty
    else Chain(Sha.parts((Chain.empty :: chains.sortBy(_.value)).map(_.value)*))

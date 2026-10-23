package frflow
package ledger

import frflow.protocol.*
import io.circe.Json

/** What a node's content means, apart from how it is worded: what a decision is bound to, and what
  * moves the decisions below it.
  */
object Meaning:

  /** What a node says itself: its content without its edges. Its parts are decided with it, but under
    * their own cause (`parts`); its parents are what it rests on (`above`), and the calls that place it
    * under them (`.under(...)`) are left out of the source it is written in. A design decision rests on
    * its parents' place, not their meaning: for it, where it is is what it says.
    */
  def own(c: Content): Content =
    if c.isDesign then c.without(_ == "parts")
    else Content(c.fields.flatMap {
      case ("parts" | "parents", _) => None
      case ("definition", j) => Some("definition" -> j.asString.fold(j)(src => Json.fromString(withoutEdges(src))))
      case f => Some(f)
    }*)
  private def withoutEdges(src: String): String = src.replaceAll("""\s*\.under\([^()]*\)""", "")

  /** Whether what the node says itself changed since it was decided (see `own`). */
  def selfChanged(decided: Content, now: Content): Boolean = own(decided).hash != own(now).hash

  /** Whether a part was added or removed since the node was decided (in any order). */
  def partsChanged(decided: Content, now: Content): Boolean =
    decided.parts.exists(_.toSet != now.parts.getOrElse(Nil).toSet)

  /** What a node rests on: its parents' chain with the chains of the definitions it uses and the
    * contracts its code calls.
    */
  def above(parentChain: Chain, otherChains: List[Chain]): Chain =
    if otherChains.isEmpty then parentChain else Chain(Sha.parts((parentChain :: otherChains.sorted).map(_.value)*))

  /** A node's chain: what its content means, together with what it rests on. A change to a node's
    * meaning puts the nodes below up for review; rewording its reason, adding an example, or editing
    * the idea reviews only the node itself.
    */
  def chain(content: Content, parentChain: Chain): Chain = chainOf(of(content), parentChain)
  def chainOf(meaning: Hash, parentChain: Chain): Chain = Chain(Sha.parts(meaning.value, parentChain.value))

  private val meaningful = Set("statement", "sources", "substitutions", "vocabulary", "uses", "governs", "formal", "op")

  /** What a node's content means, without its reason, examples or idea; and without its parent's
    * name (the chain holds the parent's meaning), so renaming a node reviews nothing below it.
    */
  def of(content: Content): Hash = content.only(meaningful).hash

  /** What a formal node means to Lean: its meaning without the words of its statement. */
  def formal(content: Content): Hash = of(content.without(_ == "statement"))

  /** A formula, a post, a rule, or a definition's terms: what Lean reads of a node. */
  def hasFormal(c: Content): Boolean =
    c("sources").exists(_.asObject.exists(_.nonEmpty)) || c("substitutions").exists(_.asArray.exists(_.nonEmpty))

  /** A node Lean reads, not out of Lean (`formal = false`). */
  def formalNode(c: Content): Boolean = !c("formal").contains(Json.False) && hasFormal(c)

  /** What Lean checks of a node (its formula), however it is worded or named. */
  def formula(c: Content): Hash = c.only(Set("sources", "substitutions")).hash

  private val DefinitionUse = """(?s)^[A-Za-z_]\w* = .*""".r

  /** What the developer decided of a node's content, without what follows from elsewhere: the types
    * it uses (`uses` also lists the definitions it calls, `name = body`, which it says), how its
    * examples print, and a proven implementation.
    */
  def decided(content: Content, provenImpl: Boolean): Hash =
    val c = own(content)
    val definitions = c("uses").flatMap(_.asArray).fold(Vector.empty[Json])(_.filter(_.asString.exists(DefinitionUse.matches)))
    val examples = c.strs("examples").map(e => Json.fromString(e.takeWhile(_ != ' ') + " — " + e.split(" — ").lastOption.getOrElse("")))
    (c.without(k => k == "uses" || k == "examples" || (provenImpl && k == "implementation")) :+
      ("definitions" -> Json.fromValues(definitions)) :+ ("examples" -> Json.fromValues(examples))).hash

  /** Whether what the developer decided of `n` changed since `d` (see `decided`). */
  def decisionMoved(d: Decision, n: SnapNode): Boolean =
    val proven = provenImpl(n)
    decided(d.content, proven) != decided(n.content, proven)

  def provenImpl(n: SnapNode): Boolean = n.implementationProof.exists(_.status == ObligationStatus.Proven)

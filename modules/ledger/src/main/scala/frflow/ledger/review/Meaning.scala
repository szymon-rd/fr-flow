package frflow
package ledger
package review

import frflow.protocol.*
import io.circe.Json

/** What a node's content means, apart from its wording: what a decision is bound to, and what moves the decisions below. */
object Meaning:
  /** Its content without parts, parents and `.refines(...)` or `.assuming(...)` calls (its causes `parts` and `above`;
    * contents recorded earlier say `.under(...)`); a design keeps its place.
    */
  private val Edges = """\s*\.(?:refines|under|assuming)\([^()]*\)"""
  def own(c: Content): Content =
    if c.isDesign then c.without(_ == "parts")
    else Content(c.fields.flatMap {
      case ("parts" | "parents", _) => None
      case ("definition", j) =>
        Some("definition" -> j.asString.fold(j)(src => Json.fromString(src.replaceAll(Edges, ""))))
      case f => Some(f)
    }*)

  def above(parentChain: Chain, otherChains: List[Chain]): Chain =
    if otherChains.isEmpty then parentChain else Chain(Sha.parts((parentChain :: otherChains.sorted).map(_.value)*))

  /** Its meaning with what it rests on: rewording its reason, adding an example or editing the idea reviews only the node. */
  def chain(content: Content, parentChain: Chain): Chain = chainOf(of(content), parentChain)
  def chainOf(meaning: Hash, parentChain: Chain): Chain = Chain(Sha.parts(meaning.value, parentChain.value))

  private val meaningful = Set("statement", "sources", "substitutions", "vocabulary", "uses", "governs", "op")

  /** Without its reason, examples, idea or parents' names (the chain holds their meaning): renaming reviews nothing below. */
  def of(content: Content): Hash = content.only(meaningful).hash

  /** What a formal node means to Lean: its meaning without the words of its statement. */
  def formal(content: Content): Hash = of(content.without(_ == "statement"))

  /** A formula, a post, a rule, or a definition's terms: what Lean reads of a node. */
  def hasFormal(c: Content): Boolean =
    c("sources").exists(_.asObject.exists(_.nonEmpty)) || c("substitutions").exists(_.asArray.exists(_.nonEmpty))

  private val DefinitionUse = """(?s)^[A-Za-z_]\w* = .*""".r

  /** Apart from what follows from elsewhere: the types it uses, how its examples print, a proven implementation. */
  def decisionMoved(d: Decision, n: SnapNode): Boolean =
    val proven = n.implementationProof.exists(_.status == ObligationStatus.Proven)
    def decided(content: Content) =
      val c = own(content)
      // A definition it calls (`name = body`) is part of what it says.
      val definitions = c("uses").flatMap(_.asArray).fold(Vector.empty[Json])(_.filter(_.asString.exists(DefinitionUse.matches)))
      val examples = c.strs("examples").map(e => Json.fromString(e.takeWhile(_ != ' ') + " — " + e.split(" — ").lastOption.getOrElse("")))
      (c.without(k => k == "uses" || k == "examples" || (proven && k == "implementation")) :+
        ("definitions" -> Json.fromValues(definitions)) :+ ("examples" -> Json.fromValues(examples))).hash
    decided(d.content) != decided(n.content)

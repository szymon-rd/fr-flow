package frflow
package ledger

import frflow.protocol.*
import io.circe.Codec

/** How a contract's code is proven: down to its code (a proven define, any running code checked
  * against it), a define not proven yet, or checked by running.
  */
enum CodeProof derives Codec.AsObject:
  case ProvenDown(define: String, running: Option[String])
  case Define(name: String, status: ObligationStatus, running: Option[String])
  case ByRunning

object CodeProof:
  def of(n: SnapNode): Option[CodeProof] =
    val impl = n.content.text("implementation")
    val running = impl.linesIterator.find(_.startsWith("runs: ")).map(r => Proofs.runningCode(r.stripPrefix("runs: ")))
    n.implementationProof match
      case Some(p) if p.status == ObligationStatus.Proven => Some(ProvenDown(p.name, running))
      case Some(p) => Some(Define(p.name, p.status, running))
      case None => Option.when(impl.nonEmpty)(ByRunning)

/** Whether nodes are proven: the one list of what is not, and the CI gate. */
object Proofs:

  /** The CI gate: every node accepted by the developer, every node proven, every example passing; rejected
    * nodes must be removed from the model, so that nothing still rests on them or is governed by them.
    */
  def complete(a: Annotated): Boolean =
    a.gone.isEmpty && a.nodes.forall(r => r.state == ReviewState.Accepted && unproven(r.node).isEmpty)

  /** What of a node is not proven or fails: the one list `status` uses. */
  def unproven(n: SnapNode): List[String] =
    def fine(s: ObligationStatus) = s == ObligationStatus.Proven
    val (ok, total) = n.examplesPassing
    n.status.filterNot(_ == CheckStatus.Proven)
      .map(st => s"its check is $st${n.messages.headOption.fold("")(m => s": ${m.linesIterator.nextOption().getOrElse("")}")}").toList ++
      n.split.map(_.complete).filterNot(c => fine(c.status)).map(c => s"its parts are not proven to make it (${c.status}: ${c.detail})") ++
      n.split.toList.flatMap(_.needed).filter(_.status == ObligationStatus.Shown).map(x => s"${x.id} is not needed for it: ${x.detail}") ++
      n.split.map(_.clash).filter(_.status == ObligationStatus.Shown).map(_ => "its parts contradict each other") ++
      Option.when(n.leaf)("nothing below proves it: add the parts that make it, or a contract") ++
      Option.when(ok != total)(s"${total - ok} example(s) fail") ++
      n.invariants.filterNot(i => fine(i.status) || i.status == ObligationStatus.Exempt).map(i => s"invariant ${i.id} is ${i.status}") ++
      n.implementationProof.filterNot(p => fine(p.status)).map(p => s"its implementation ${p.name} is ${p.status}: not proven to meet the contract") ++
      n.rootImpl.filterNot(p => fine(p.status)).map(p => s"root_impl is ${p.status}: the root is not proven of the code") ++
      n.expectations.filterNot(e => fine(e.status)).map(e => s"an expectation is ${e.status}") ++
      // A root doing nothing meets says only what must not happen: the system can drop every feature unnoticed.
      n.idle.map(what => s"Lean shows doing nothing meets it ($what): say what users can do, so the root is stated as exactly")

  /** Running code as named in a summary: `LoanIndex(...).borrow` as `LoanIndex.borrow`. */
  def runningCode(wiring: String): String =
    val body = wiring.trim.replaceFirst("""^\([^()]*\)\s*=>\s*|^\w+\s*=>\s*""", "")
    // The text outside parentheses.
    val (flat, _) = body.foldLeft(("", 0)) { case ((out, depth), c) =>
      if c == '(' then (out, depth + 1) else if c == ')' then (out, depth - 1) else if depth == 0 then (out + c, depth) else (out, depth)
    }
    val name = flat.replace(".value", "").replaceAll("\\s+", " ").trim
    if name.nonEmpty && name.length <= 60 then name else body.take(57) + "…"

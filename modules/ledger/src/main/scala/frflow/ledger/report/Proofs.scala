package frflow
package ledger
package report

import frflow.protocol.*

object Proofs:
  /** What of a node's tested code is not shown: a generated case that fails, a part of the contract no case reached,
    * or no test yet.
    */
  def tests(n: SnapNode): List[String] =
    if !CodeProof.run(n) then Nil
    else
      val model = CodeProof.of(n).exists { case _: CodeProof.Model => true; case _ => false }
      val (whose, against) = if model then ("its implementations'", "the model") else ("its code's", "the contract")
      n.tested.fold(List(if model then "its implementations are not tested yet: run check" else "its code is not tested yet: run check")) { r =>
        r.failure.map(f => s"${if model then "a generated run differs from the model" else "its code fails a generated case"}: ${f.shown}: ${f.why}").toList ++
          r.unreached.map(c => s"$whose tests never reached a part of $against: ${c.part} (add an example, or a generator)")
      }

  /** The CI gate: some node (a project still in its conversation is not done), IDEA.md accepted, every node accepted and
    * proven, every example passing; rejected nodes removed from the model, so that nothing rests on them or is governed by them.
    */
  def complete(a: Annotated): Boolean =
    a.nodes.nonEmpty && a.idea.forall(_.state == ReviewState.Accepted) &&
      a.gone.isEmpty && a.nodes.forall(r => r.state == ReviewState.Accepted && unproven(r.node).isEmpty)

  /** What of a node is not proven or fails, as `status` lists it. */
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
      tests(n) ++
      n.expectations.filterNot(e => fine(e.status)).map(e => s"an expectation is ${e.status}") ++
      // A root doing nothing meets says only what must not happen: the system can drop every feature unnoticed.
      n.idle.map(what => s"Lean shows doing nothing meets it ($what): say what users can do, so the root is stated as exactly")

  /** Running code as named in a summary: `LoanIndex(...).borrow` as `LoanIndex.borrow`. */
  def runningCode(wiring: String): String =
    val body = wiring.trim.replaceFirst("""^\([^()]*\)\s*=>\s*|^\w+\s*=>\s*""", "")
    val (outside, _) = body.foldLeft(("", 0)) { case ((out, depth), c) =>
      if c == '(' then (out, depth + 1) else if c == ')' then (out, depth - 1) else if depth == 0 then (out + c, depth) else (out, depth)
    }
    val name = outside.replace(".value", "").replaceAll("\\s+", " ").trim
    if name.nonEmpty && name.length <= 60 then name else body.take(57) + "…"

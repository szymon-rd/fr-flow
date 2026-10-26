package frflow.cli
package text

import frflow.api.*
import frflow.protocol.*

/** The lines every view closes with: the counts, the proofs and what is trusted, what waits; `more`, what layers on top
  * add to what waits.
  */
object SummaryText:
  def lines(s: Overview, st: Style, more: List[String] = Nil): List[String] =
    def some(n: Int, what: String, tone: String => String = identity) = Option.when(n > 0)(tone(s"$n $what"))
    val counts = (Some(st.green(s"${s.accepted} accepted")) :: List(some(s.review, "to review", st.yellow),
      some(s.proposed, "proposed", st.cyan), some(s.rejected, "rejected", st.red), some(s.gone, "gone", st.red))).flatten
    def ratio(ok: Int, of: Int) = if ok == of then st.green(s"$ok/$of") else st.red(s"$ok/$of")
    val rootImpl = s.rootImpl.map {
      case ObligationStatus.Proven => st.green("proven")
      case ObligationStatus.Unchecked => st.dim("unchecked")
      case other => st.red(other.toString)
    }
    val proofs = List(Option.when(s.splits > 0)(s"splits ${ratio(s.splitsProven, s.splits)} proven"),
      Option.when(s.contracts > 0)(s"contracts ${ratio(s.contractsProvenDown, s.contracts)} proven down to their code"),
      Option.when(s.contractsTested > 0)(s"code tested against its contract ${ratio(s.testsPassing, s.contractsTested)}"),
      Option.when(s.modelsRun > 0)(s"boundaries' implementations run against their models ${ratio(s.modelsPassing, s.modelsRun)}"),
      rootImpl.map(r => s"root_impl $r"),
      Option.when(s.runEveryCall + s.runSampled + s.runNotChecked > 0)("at run time: " + List(
        some(s.runEveryCall, "checked on every call", identity), some(s.runSampled, "sampled", identity),
        some(s.runNotChecked, "not checked (proven)", identity)).flatten.mkString(", ")),
      Option.when(s.examplesInLean > 0)(s"examples ${ratio(s.examplesAgreeing, s.examplesInLean)} agree in Lean"),
      Some(s"trusted: ${s.trusted.filterNot(s.tested.contains) match { case Nil => "nothing"; case ts => ts.mkString(", ") }}" +
        (if s.tested.isEmpty then "" else s"; tested, not proven: ${s.tested.mkString(", ")}")),
      some(s.unproven, "with something unproven", st.red), some(s.warnings, "warning(s)", st.red),
      some(s.unsigned, "decision(s) not signed", st.red)).flatten
    val waits = List(
      Option.when(s.forDeveloper > 0)(st.yellow(s"${s.forDeveloper} for the developer") +
        (if s.idea.exists(_ != ReviewState.Accepted) then " (IDEA.md first)" else "") +
        (if s.mechanical > 0 then s" (${s.mechanical} mechanical: confirm)" else ""))).flatten ++ more
    val sep = if st.unicode then s" ${st.dot} " else ", "
    // Before the first node, the project is IDEA.md: what comes next is said instead of the counts.
    val start = if s.nodes > 0 then Nil
      else List(s.idea match
        case None => "No IDEA.md yet: write in it what the system is for, then accept it; the root comes next."
        case Some(ReviewState.Accepted) => "IDEA.md is accepted: the root comes next."
        case Some(_) => "IDEA.md waits for you: read it, then accept IDEA.")
    val head = if s.nodes > 0 then List(s"${st.bold(s.name)}: ${s.nodes} nodes${sep}${counts.mkString(sep)}", proofs.mkString(sep))
      else List(s"${st.bold(s.name)}: no nodes yet") ++ start
    (head :+ (if waits.isEmpty then (if s.complete then st.green(s"Nothing waits: every node is accepted and proven${if s.tested.isEmpty then "" else ", or its code tested"}.") else "Nothing waits for a decision.")
      else s"Waiting: ${waits.mkString(sep)}")).flatMap(Lines.para(_, st, indent = 0)) ++ Option.when(s.nodes > 0)(legend(st))

  /** What the marks before the nodes say, on one line. */
  def legend(st: Style): String =
    st.dim("marks: ") + List(st.proven -> "proven or tested", st.failed -> "fails", st.open -> "not proven",
      "?" -> "not checked yet", st.dim(st.dot) -> "nothing to prove", "!" -> "what to do").map((m, w) => s"$m ${st.dim(w)}").mkString("  ")

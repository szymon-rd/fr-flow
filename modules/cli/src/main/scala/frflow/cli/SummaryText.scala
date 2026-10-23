package frflow.cli

import frflow.api.*
import frflow.protocol.ObligationStatus

/** The lines every view closes with: the counts, the proofs and what is trusted, what waits for whom. */
object SummaryText:
  def lines(s: Overview, st: Style): List[String] =
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
      rootImpl.map(r => s"root_impl $r"),
      Option.when(s.examplesInLean > 0)(s"examples ${ratio(s.examplesAgreeing, s.examplesInLean)} agree in Lean"),
      Some(s"trusted: ${if s.trusted.isEmpty then "nothing" else s.trusted.mkString(", ")}"),
      some(s.unproven, "with something unproven", st.red), some(s.warnings, "warning(s)", st.red),
      some(s.unsigned, "decision(s) not signed", st.red)).flatten
    val waits = List(
      Option.when(s.forDeveloper > 0)(st.yellow(s"${s.forDeveloper} for the developer") +
        (if s.mechanical > 0 then s" (${s.mechanical} mechanical: confirm)" else "")),
      some(s.withAgent, "asked of the agent", st.magenta), some(s.forAgent, "for the agent", st.magenta),
      some(s.openRequests, "open request(s)"), some(s.answers, "answer(s) to read")).flatten
    val sep = if st.unicode then s" ${st.dot} " else ", "
    List(
      s"${st.bold(s.name)}: ${s.nodes} nodes${sep}${counts.mkString(sep)}",
      proofs.mkString(sep),
      if waits.isEmpty then (if s.complete then st.green("Nothing waits: every node is accepted and proven.") else "Nothing waits for a decision.")
      else s"Waiting: ${waits.mkString(sep)}").flatMap(Lines.para(_, st, indent = 0))

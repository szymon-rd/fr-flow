package frflow.cli
package text

import frflow.api.*
import frflow.protocol.*

/** The lines every view closes with: the counts, the proofs and what is trusted, what waits; `more`, what layers on top
  * add to what waits.
  */
object SummaryText:
  def lines(s: Overview, st: Style, more: List[String] = Nil): List[String] =
    val sep = if st.unicode then s" ${st.dot} " else ", "
    def some(n: Int, what: String, tone: String => String = identity) = Option.when(n > 0)(tone(s"$n $what"))
    val counts = (Some(st.green(s"${s.accepted} accepted")) :: List(some(s.review, "to review", st.yellow),
      some(s.proposed, "proposed", st.cyan), some(s.rejected, "rejected", st.red), some(s.gone, "gone", st.red))).flatten
    def ratio(ok: Int, of: Int) = if ok == of then st.green(s"$ok/$of") else st.red(s"$ok/$of")
    val rootImpl = s.rootImpl.map {
      case ObligationStatus.Proven => st.green("proven")
      case ObligationStatus.Unchecked => st.dim("unchecked")
      case other => st.red(other.toString)
    }
    // A line each: what is proven, what is tested, what is trusted.
    val proofs = List(Option.when(s.splits > 0)(s"splits ${ratio(s.splitsProven, s.splits)}"),
      Option.when(s.contracts > 0)(s"claims down to their code ${ratio(s.contractsProvenDown, s.contracts)}"),
      rootImpl.map(r => s"root_impl $r"), consistency(s, st)).flatten
    val tests = List(
      Option.when(s.contractsTested > 0)(s"code against its claims ${ratio(s.testsPassing, s.contractsTested)}"),
      Option.when(s.modelsRun > 0)(s"implementations against their models ${ratio(s.modelsPassing, s.modelsRun)}"),
      Option.when(s.examplesInLean > 0)(s"examples in Lean ${ratio(s.examplesAgreeing, s.examplesInLean)}"),
      Option.when(s.runEveryCall + s.runSampled + s.runNotChecked > 0)("at run time " + List(
        some(s.runEveryCall, "checked on every call", identity), some(s.runSampled, "sampled", identity),
        some(s.runNotChecked, "not checked (proven)", identity)).flatten.mkString(", "))).flatten
    val trust = (trusted(s) match { case Nil => "nothing"; case ts => ts.mkString(", ") }) +
      (if s.tested.isEmpty then "" else s"; tested, not proven: ${s.tested.mkString(", ")}")
    val problems = List(some(s.unproven, "with something unproven", st.red), some(s.warnings, "warning(s)", st.red),
      some(s.unsigned, "decision(s) not signed", st.red)).flatten
    val checked = List(Option.when(proofs.nonEmpty)(s"Proofs: ${proofs.mkString(sep)}"),
      Option.when(tests.nonEmpty)(s"Tests: ${tests.mkString(sep)}"), Some(s"Trusted: $trust"),
      Option.when(problems.nonEmpty)(problems.mkString(sep))).flatten
    val waits = List(
      Option.when(s.forDeveloper > 0)(st.yellow(s"${s.forDeveloper} for the developer") +
        (if s.idea.exists(_ != ReviewState.Accepted) then " (IDEA.md first)" else "") +
        (if s.mechanical > 0 then s" (${s.mechanical} mechanical: confirm)" else ""))).flatten ++ more
    // Before the first node, the project is IDEA.md: what comes next is said instead of the counts.
    val start = if s.nodes > 0 then Nil
      else List(s.idea match
        case None => "No IDEA.md yet: write in it what the system is for, then accept it; the root comes next."
        case Some(ReviewState.Accepted) => "IDEA.md is accepted: the root comes next."
        case Some(_) => "IDEA.md waits for you: read it, then accept IDEA.")
    val head = if s.nodes > 0 then s"${st.bold(s.name)}: ${s.nodes} nodes${sep}${counts.mkString(sep)}" :: checked
      else List(s"${st.bold(s.name)}: no nodes yet") ++ start
    (head :+ (if waits.isEmpty then (if s.complete then st.green(s"Nothing waits: every node is accepted and proven${if s.tested.isEmpty then "" else ", or its code tested"}.") else "Nothing waits for a decision.")
      else s"Waiting: ${waits.mkString(sep)}")).flatMap(Lines.para(_, st, indent = 0)) ++ Option.when(s.nodes > 0)(legend(st))

  /** Whether the statements are shown to hold together, and to rest on nothing vacuous; how many groups miss it. */
  private def consistency(s: Overview, st: Style): Option[String] =
    Option.when(s.nodes > 0)(s.consistency.fold(st.dim("consistency not checked yet")) { c =>
      val missing = c.items.count(_.status != ObligationStatus.Proven)
      val together = if c.proven then st.green("consistency proven") else st.red("consistency not proven")
      val vacuous = if c.notVacuous then "nothing vacuous" else st.red("something may be vacuous")
      val what = if missing == 0 then "" else s" ($missing open: check says which)"
      s"$together, $vacuous$what"
    })

  /** What is trusted, not proven: the assumptions the root rests on, the boundaries' models, the facts. */
  private def trusted(s: Overview): List[String] =
    val facts = Option.when(s.facts.nonEmpty)(s"${s.facts.map(_.value).mkString(", ")} (facts)")
    s.trusted.filterNot(s.tested.contains).map(_.value) ++ s.models.map(m => s"${m.value} (a model)") ++ facts

  /** What the marks before the nodes say, on one line. */
  def legend(st: Style): String =
    st.dim("marks: ") + List(st.proven -> "proven or tested", st.failed -> "fails", st.open -> "not proven",
      "?" -> "not checked yet", st.dim(st.dot) -> "nothing to prove", "!" -> "to decide, or what to do")
      .map((m, w) => s"$m ${st.dim(w)}").mkString("  ")

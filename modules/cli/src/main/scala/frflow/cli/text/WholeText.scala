package frflow.cli.text

import frflow.api.view.whole.*
import frflow.cli.say.{Findings, Tested, Values}
import frflow.cli.term.{Marks, Style}
import frflow.core.consistency.{Vacuity, Witness}
import frflow.eval.run.OnCode

/** The theory as a whole (`status`, `check`): its consistency by group, with each open value's witness; the states
  * each store starts in; what is shown possible; and the examples, against the claims and the code.
  */
object WholeText:
  def lines(w: WholeView, st: Style, full: Boolean): List[String] =
    Lines.section("Consistency: a meaning for what is open under which every statement holds",
        w.groups.flatMap(group(_, st, full)), st) ++
      Lines.section("Shown possible", w.possible.flatMap((v, o) => ProofText.obligation(o, st, full)
        .updated(0, s"${possible(v)}: ${Findings.obligation(o.state)}")), st) ++
      Lines.section("Examples", w.examples.map(example(_, st)), st)

  private def group(g: GroupView, st: Style, full: Boolean): List[String] =
    val status = g.status match
      case GroupStatus.Proven       => st.green("proven")
      case GroupStatus.Evidence(ts) => st.yellow(s"evidence only: ${ts.map(_.value).mkString(", ")} tested, not proven")
      case GroupStatus.NotProven    => st.red("consistency not proven")
    s"${g.statements.mkString(", ")}: $status" :: (g.witnesses.map(w => s"  ${witness(w)}") ++
      (if g.status == GroupStatus.Proven && !full then Nil else Findings.messages(g.check.messages, full)))

  private def witness(w: Witness): String = w match
    case Witness.Equation(s, from, _) => s"${s.value}: as $from defines it"
    case Witness.Bound(s, from, _)    => s"${s.value}: at the bound $from sets"
    case Witness.Tested(s)            => s"${s.value}: its tested Scala (evidence, not proof)"
    case Witness.Missing(s)           => s"${s.value}: no witness (prove the group consistent in a proof file)"
    case Witness.Empty(s)             => s"${s.value}: the empty list"

  private def possible(v: Vacuity): String = v match
    case Vacuity.Inhabited(id, ty)       => s"$id admits a value of ${Values.ty(ty)}"
    case Vacuity.Satisfiable(id, i, _)   => s"condition ${i + 1} of $id can hold"

  /** An example's line: `+` it passes, `x` it fails (on the code, or the claims contradict it, or give both it and
    * its negation), `o` the claims do not decide it and the code does not fail it (reported: nothing depends on an
    * example, owner §18).
    */
  private def example(e: ExampleView, st: Style): String =
    val rocq = e.onClaims match
      case OnClaims.ScalaOnly                        => "checked in Scala only (it gives values)"
      case c @ OnClaims.Rocq(_, _) if c.inconsistent => "Rocq: the claims are inconsistent here: they give both it " +
          "and its negation"
      case c @ OnClaims.Rocq(_, _) if c.contradicted => "Rocq: the claims contradict it"
      case OnClaims.Rocq(c, _)                       => s"Rocq: ${Findings.obligation(c.state)}" +
          (if ExampleView.shown(c.state) then "" else ", not decided by the claims")
    val code = if e.onCode == OnCode.Holds then "" else s"; ${Tested.onCode(e.onCode)}"
    e.outcome match
      case ExampleOutcome.Passes    => s"${Marks.proven(st)} ${e.name}  ${st.dim(rocq)}$code"
      case ExampleOutcome.Undecided => s"${Marks.open(st)} ${e.name}  ${st.dim(rocq)}$code"
      case ExampleOutcome.Fails     => s"${Marks.failed(st)} ${e.name}  ${st.red(rocq + code)}"

  /** Whether everything about the whole is as it should be: what `check` exits on beside the nodes. An example the
    * claims do not decide is no failure.
    */
  def fine(w: WholeView): Boolean = w.groups.forall(_.status == GroupStatus.Proven) &&
    w.examples.forall(_.outcome != ExampleOutcome.Fails)

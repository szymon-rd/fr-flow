package frflow.cli.say

import frflow.api.node.tests.*
import frflow.core.example.Given
import frflow.eval.EvalError
import frflow.eval.run.{Broken, OnCode}

/** What testing before production found, in words: the cases, the outcome (the smallest failing case, where it was
  * drawn), the parts no case reached, the notes. Not tested yet is said apart from failing a generated case.
  */
object Tested:
  val NotYet: String = "not tested yet: run check"
  val Moved: String = "the claim changed and its code did not: the code fails a case of the changed claim"

  /** `movedUnderCode`: the claim changed and its code did not, so a failing case is the claim's change. */
  def lines(t: TestView, movedUnderCode: Boolean): List[String] =
    head(t) :: (outcome(t.outcome, movedUnderCode) :: shortfall(t.cases).toList) ++
      t.unreached.map(target) ++ t.notes.map(note)

  def head(t: TestView): String = t.against match
    case Against.Claim(n)    => s"tested on ${t.cases.tried} generated cases (seed ${t.cases.seed}) against $n"
    case Against.Model(n, i) => s"tested on ${t.cases.tried} generated runs (seed ${t.cases.seed}) against the model " +
        s"$n says (implementation ${i + 1})"

  def outcome(o: TestOutcome, movedUnderCode: Boolean): String = o match
    case TestOutcome.Passed        => "every case meets it"
    case TestOutcome.Failed(f)     => failed(f, movedUnderCode)
    case TestOutcome.NotChecked(e) => s"not checked: the statement has no Scala value to test against (${eval(e)})"

  def failed(f: FailedCase, movedUnderCode: Boolean): String = f match
    case FailedCase.Call(in, gs, broke, from) =>
      val head = if movedUnderCode then Tested.Moved else "fails a generated case"
      s"$head: (${Values.all(in)})${givens(gs)}: ${broken(broke)} (${drawn(from)})"
    case FailedCase.Run(start, steps, d, from) =>
      s"a generated run differs from the model: from ${Values.value(start)}, ${steps.map(step).mkString(", ")}: " +
        s"${difference(d)} (${drawn(from)})"

  private def givens(gs: List[Given]): String =
    if gs.isEmpty then ""
    else gs.map(g => s"${g.symbol.value} = ${Values.value(g.value)}").mkString(" given ", ", ", "")

  def broken(b: Broken): String = b match
    case Broken.Post            => "its result breaks the claim"
    case Broken.Always(id)      => s"it breaks $id"
    case Broken.Assumption(id)  => s"the assumption $id does not hold of the values it ran with"
    case Broken.NotEvaluated(e) => s"the claim could not be evaluated: ${eval(e)}"
    case Broken.Threw(m)        => s"the code threw: $m"

  def eval(e: EvalError): String = e match
    case EvalError.Quantified  => "it quantifies over a type"
    case EvalError.Unbound(s)  => s"nothing binds ${s.value}"
    case EvalError.NoDefine(d) => s"the define ${d.value} is missing"
    case EvalError.NoCase      => "a match has no arm for the value"
    case EvalError.NoModel(m)  => s"no model ${m.value}"
    case EvalError.Steps       => "it is a program's steps, run rather than evaluated"

  def onCode(o: OnCode): String = o match
    case OnCode.Holds           => "the code holds it"
    case OnCode.Fails           => "the code does not hold it"
    case OnCode.NotEvaluated(e) => s"not evaluated: ${eval(e)}"
    case OnCode.Abstract(ds)    => s"it speaks of Declarations (${ds.map(_.value).mkString(", ")}): checked against " +
        "the claims only"
    case OnCode.Threw(m)        => s"the code threw: $m"

  private def difference(d: Difference): String = d match
    case Difference.Call(s, impl, model) => s"at ${step(s)} the implementation ${ran(impl)}, the model ${ran(model)}"
    case Difference.State(impl, model)   =>
      s"the implementation holds ${Values.value(impl)} where the model holds ${Values.value(model)}"
    case Difference.NotRun(m)            => s"the implementation was not made or not read back: $m"

  private def ran(r: Ran): String = r match
    case Ran.Gave(v)   => s"gave ${Values.value(v)}"
    case Ran.Failed(e) => s"failed with ${Values.value(e)}"
    case Ran.Threw(m)  => s"threw $m"

  private def step(s: Step): String = s"${s.boundary.value}.${s.op.value}(${Values.all(s.args)})"
  private def drawn(d: Drawn): String = s"seed ${d.seed}, case ${d.index}, size ${d.size}"

  private def shortfall(c: Cases): Option[String] =
    Option.when(c.shortfall > 0)(s"only ${c.tried} of ${c.asked} cases could be drawn")

  def target(t: Target): String = s"never reached: ${reach(t.reach)} (part ${t.path.mkString(".")})"

  private def reach(r: Reach): String = r match
    case Reach.Premise      => "its premise holding"
    case Reach.Side(i)      => s"side ${i + 1} of an or"
    case Reach.Branch(held) => if held then "the condition holding" else "the condition not holding"
    case Reach.Arm(i)       => s"arm ${i + 1} of a match"
    case Reach.NonEmpty     => "a list or option not empty"
    case Reach.Called(op)   => s"a call of ${op.value}"

  def note(n: Note): String = n match
    case Note.Given(ty, says)    => s"note: the generator given for ${Values.ty(ty)}${says.fold("")(s => s": $s")}"
    case Note.NeverMade(ty, vs) =>
      s"note: the generator of ${Values.ty(ty)} never makes the examples' ${Values.all(vs)}"
    case Note.NothingToVary      => "note: nothing varies between cases"

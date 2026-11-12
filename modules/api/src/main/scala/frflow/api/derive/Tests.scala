package frflow.api.derive

import frflow.api.node.tests.*
import frflow.testing.report.{Drawn as From, Failure, Note as Noted, Outcome, Reach as Reached, Target as Aim,
  TestReport}

/** What testing found, as the front ends see it: each of `testing.report`'s values as its view, case for case. */
private[api] object Tests:
  def of(r: TestReport): TestView = TestView(Cases(r.count.asked, r.count.tried, r.seed.value), r.against,
    outcome(r.outcome), r.unreached.map(target), r.notes.map(note))

  private def outcome(o: Outcome): TestOutcome = o match
    case Outcome.Passed        => TestOutcome.Passed
    case Outcome.Failed(f)     => TestOutcome.Failed(failure(f))
    case Outcome.NotChecked(e) => TestOutcome.NotChecked(e)

  def failure(f: Failure): FailedCase = FailedCase(f.inputs, f.givens, f.broke, drawn(f.from))

  private def drawn(d: From): Drawn = Drawn(d.seed.value, d.index, d.size)
  private def target(t: Aim): Target = Target(t.at.path, t.reach match
    case Reached.Premise   => Reach.Premise
    case Reached.Side(i)   => Reach.Side(i)
    case Reached.Branch(h) => Reach.Branch(h)
    case Reached.Arm(i)    => Reach.Arm(i)
    case Reached.NonEmpty  => Reach.NonEmpty)

  private def note(n: Noted): Note = n match
    case Noted.Given(made)       => Note.Given(made.ty, made.says)
    case Noted.NeverMade(ty, vs) => Note.NeverMade(ty, vs)
    case Noted.NothingToVary     => Note.NothingToVary

package frflow.api.derive

import frflow.api.node.tests.*
import frflow.core.name.{ModelName, SymbolName}
import frflow.testing.model.{Difference as Diff, Ran as Did, Step as Called}
import frflow.testing.report.{Against as On, Drawn as From, Failure, Note as Noted, Outcome, Reach as Reached,
  Target as Aim, TestReport}

/** What testing found, as the front ends see it: each of `testing.report`'s values as its view, case for case. */
private[api] object Tests:
  /** Of a report, a model's runs naming the model's operations (`operations`). */
  def of(r: TestReport, operations: ModelName => List[SymbolName]): TestView =
    TestView(Cases(r.count.asked, r.count.tried, r.seed.value), against(r.against, operations),
    outcome(r.outcome), r.unreached.map(target), r.notes.map(note))

  private def against(a: On, operations: ModelName => List[SymbolName]): Against = a match
    case On.Claim(n)    => Against.Claim(n)
    case On.Model(n, m) => Against.Model(n, m, operations(m))

  private def outcome(o: Outcome): TestOutcome = o match
    case Outcome.Passed        => TestOutcome.Passed
    case Outcome.Failed(f)     => TestOutcome.Failed(failure(f))
    case Outcome.NotChecked(e) => TestOutcome.NotChecked(e)

  def failure(f: Failure): FailedCase = f match
    case Failure.Call(in, gs, broke, from) => FailedCase.Call(in, gs, broke, drawn(from))
    case Failure.Run(s, steps, d, from)    => FailedCase.Run(s, steps.map(step), difference(d), drawn(from))

  private def drawn(d: From): Drawn = Drawn(d.seed.value, d.index, d.size)
  private def step(s: Called): Step = Step(s.op, s.args)

  private def difference(d: Diff): Difference = d match
    case Diff.Call(s, impl, model) => Difference.Call(step(s), ran(impl), ran(model))
    case Diff.State(impl, model)   => Difference.State(impl, model)
    case Diff.NotRun(message)      => Difference.NotRun(message)

  private def ran(r: Did): Ran = r match
    case Did.Gave(v)    => Ran.Gave(v)
    case Did.Failed(e)  => Ran.Failed(e)
    case Did.Threw(m)   => Ran.Threw(m)

  private def target(t: Aim): Target = Target(t.at.path, t.reach match
    case Reached.Premise   => Reach.Premise
    case Reached.Side(i)   => Reach.Side(i)
    case Reached.Branch(h) => Reach.Branch(h)
    case Reached.Arm(i)    => Reach.Arm(i)
    case Reached.NonEmpty  => Reach.NonEmpty
    case Reached.Called(o) => Reach.Called(o))

  private def note(n: Noted): Note = n match
    case Noted.Given(made)       => Note.Given(made.ty, made.says)
    case Noted.NeverMade(ty, vs) => Note.NeverMade(ty, vs)
    case Noted.NothingToVary     => Note.NothingToVary

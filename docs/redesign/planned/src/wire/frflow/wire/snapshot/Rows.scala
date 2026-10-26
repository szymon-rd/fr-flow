package frflow.wire.snapshot

import frflow.core.analysis.{Assumed, Shown, Tested}
import frflow.core.expr.Value
import frflow.decision.content.{Content, FieldValue}
import frflow.eval.EvalError
import frflow.eval.run.{Agreement, Broken, ExampleResult}
import frflow.proof.lean.lower.LowerObligation
import frflow.proof.verdict.{ObligationStatus, Result}
import frflow.testing.{Against, TestReport}

/** The one mapping from domain values to the export's rows, each written out here: a rename in the domain does not
  * move the export.
  */
object Rows:
  def content(c: Content): List[(String, FieldRow)] = c.fields.map((k, v) => k -> (v match
    case FieldValue.Text(t)    => FieldRow.Text(t)
    case FieldValue.Texts(ts)  => FieldRow.Texts(ts)
    case FieldValue.Record(fs) => FieldRow.Record(fs)))

  def code(s: Shown): CodeRow = CodeRow(s.proven.map(_.value), s.tested.map(tested), s.assumed.map(assumed))

  def example(e: ExampleResult): ExampleRow = ExampleRow(e.index, agreement(e.onPromise), e.onCode.map(agreement))

  def obligation(r: Result, statement: String): ObligationRow =
    ObligationRow(LowerObligation.name(r.name).text, status(r.status), statement)

  def test(t: TestReport): TestRow = TestRow(t.cases, t.seed.value, against(t.against), t.failure.isDefined)

  /** A value as today's `Example.show` writes it: `"text"`, `Some(x)`, `List(a, b)`, `Map(k -> v)`, `ctor(a, b)`. */
  def shown(v: Value): String = v match
    case Value.Bool(b)       => b.toString
    case Value.Num(n)        => n.toString
    case Value.Str(s)        => "\"" + s + "\""
    case Value.Unit          => "()"
    case Value.Data(c, Nil)  => c.value
    case Value.Data(c, fs)   => fs.map(shown).mkString(s"${c.value}(", ", ", ")")
    case Value.Many(xs)      => xs.map(shown).mkString("List(", ", ", ")")
    case Value.Maybe(x)      => x.fold("None")(y => s"Some(${shown(y)})")
    case Value.Pairs(es)     => es.map((k, x) => s"${shown(k)} -> ${shown(x)}").mkString("Map(", ", ", ")")
    case Value.Tuple(xs)     => xs.map(shown).mkString("(", ", ", ")")
    case Value.World(ss, fs) => ss.map((m, s) => s"${m.value}: ${shown(s)}").mkString("World(", ", ", s"; faults $fs)")

  private def tested(t: Tested): String = t match
    case Tested.Plain     => "plain"
    case Tested.Beside(d) => s"beside ${d.value}"
    case Tested.Own(i)    => s"own $i"

  private def assumed(a: Assumed): String = a match
    case Assumed.Promise    => "promise"
    case Assumed.Outside(i) => s"outside $i"

  private def agreement(a: Agreement): AgreementRow = a match
    case Agreement.Agrees         => AgreementRow("agrees", None)
    case Agreement.PromiseRefuses => AgreementRow("promise-refuses", None)
    case Agreement.PromiseAccepts => AgreementRow("promise-accepts", None)
    case Agreement.Returned(v)    => AgreementRow("returned", Some(shown(v)))
    case Agreement.Breaks(b)      => AgreementRow("breaks", Some(broken(b)))

  private def broken(b: Broken): String = b match
    case Broken.Post            => "post"
    case Broken.Check           => "check"
    case Broken.Invariant(i)    => s"invariant ${i.value}"
    case Broken.Assumption(i)   => s"assumption ${i.value}"
    case Broken.NotEvaluated(e) => s"not evaluated: ${notEvaluated(e)}"
    case Broken.Threw(m)        => s"threw: $m"

  private def notEvaluated(e: EvalError): String = e match
    case EvalError.Quantified  => "it quantifies"
    case EvalError.Unbound(s)  => s"${s.value} is not bound"
    case EvalError.NoDefine(d) => s"no define ${d.value}"

  /** As today's statuses are written (`not-shown`). */
  private def status(s: ObligationStatus): String = s match
    case ObligationStatus.Proven      => "proven"
    case ObligationStatus.Open        => "open"
    case ObligationStatus.Failed      => "failed"
    case ObligationStatus.Shown       => "shown"
    case ObligationStatus.NotShown    => "not-shown"
    case ObligationStatus.Unevaluated => "unevaluated"
    case ObligationStatus.Unchecked   => "unchecked"
    case ObligationStatus.Timeout     => "timeout"

  private def against(a: Against): String = a match
    case Against.Promise(n)  => s"promise ${n.value}"
    case Against.Define(d)   => s"define ${d.value}"
    case Against.Model(n, i) => s"model ${n.value} realization $i"

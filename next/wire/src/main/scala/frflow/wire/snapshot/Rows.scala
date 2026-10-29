package frflow.wire.snapshot

import frflow.core.checking.{Assumed, Shown, Tested}
import frflow.core.consistency.{Group, Standing, Witness}
import frflow.core.example.Example
import frflow.core.expr.{Side, Value}
import frflow.decision.content.{Content, FieldValue}
import frflow.eval.EvalError
import frflow.eval.run.{Broken, OnCode}
import frflow.proof.lean.lower.LowerObligation
import frflow.proof.verdict.{ObligationStatus, Result}
import frflow.testing.report.{Against, TestReport}

/** The one mapping from domain values to the export's rows, each written out here: a rename in the domain does not
  * move the export.
  */
object Rows:
  def content(c: Content): List[(String, FieldRow)] = c.fields.map((k, v) => k -> field(v))

  def field(v: FieldValue): FieldRow = v match
    case FieldValue.Text(t)    => FieldRow.Text(t)
    case FieldValue.Texts(ts)  => FieldRow.Texts(ts)
    case FieldValue.Record(fs) => FieldRow.Record(fs)

  def code(s: Shown): CodeRow = CodeRow(s.proven.map(_.value), s.tested.map(tested), s.assumed.map(assumed))

  def example(e: Example, onClaims: Option[ObligationStatus], onCode: OnCode): ExampleRow =
    ExampleRow(e.name, if e.givens.nonEmpty then "checked in Scala only" else onClaims.fold("unchecked")(status),
      code(onCode))

  def group(g: Group.Sharing): GroupRow =
    GroupRow(g.statements.map(_.value), g.open.map(_.value), g.provided.map(_.value), g.witnesses.map(witness),
      standing(g.standing))

  def obligation(r: Result, statement: String): ObligationRow =
    ObligationRow(LowerObligation.name(r.name).text, status(r.status), statement)

  def test(t: TestReport): TestRow = TestRow(t.cases, t.seed.value.toString, against(t.against), t.failure.isDefined)

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
    case Value.Inject(s, x)  => s"${if s == Side.Error then "Left" else "Right"}(${shown(x)})"
    case Value.World(ss, fs) => ss.map((m, s) => s"${m.value}: ${shown(s)}").mkString("World(", ", ", s"; faults $fs)")

  private def tested(t: Tested): String = t match
    case Tested.Plain    => "plain"
    case Tested.Model(m) => s"model ${m.value}"

  private def assumed(a: Assumed): String = a match
    case Assumed.Assumption => "assumption"

  private def code(c: OnCode): String = c match
    case OnCode.Holds           => "holds"
    case OnCode.Fails           => "fails"
    case OnCode.NotEvaluated(e) => s"not-evaluated: ${notEvaluated(e)}"
    case OnCode.Abstract(ds)    => s"abstract: ${ds.map(_.value).mkString(", ")}"
    case OnCode.Threw(m)        => s"threw: $m"

  private def witness(w: Witness): String = w match
    case Witness.Equation(s, from, _) => s"${s.value}: the equation of ${from.value}"
    case Witness.Bound(s, from, _)    => s"${s.value}: the bound of ${from.value}"
    case Witness.Tested(s)            => s"${s.value}: tested Scala (evidence)"
    case Witness.Missing(s)           => s"${s.value}: none"

  private def standing(s: Standing): String = s match
    case Standing.Witnessed    => "witnessed"
    case Standing.Evidence(ts) => s"evidence: ${ts.map(_.value).mkString(", ")} tested"
    case Standing.Unwitnessed(_) => "consistency not proven"

  def broken(b: Broken): String = b match
    case Broken.Post            => "post"
    case Broken.Always(i)       => s"always ${i.value}"
    case Broken.Assumption(i)   => s"assumption ${i.value}"
    case Broken.NotEvaluated(e) => s"not evaluated: ${notEvaluated(e)}"
    case Broken.Threw(m)        => s"threw: $m"

  private def notEvaluated(e: EvalError): String = e match
    case EvalError.Quantified  => "it quantifies"
    case EvalError.Unbound(s)  => s"${s.value} is not bound"
    case EvalError.NoDefine(d) => s"no define ${d.value}"
    case EvalError.NoCase      => "no arm for its case"
    case EvalError.NoModel(m)  => s"no state of ${m.value}"
    case EvalError.Steps       => "it is a program's steps"

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
    case Against.Claim(n)    => s"claim ${n.value}"
    case Against.Model(n, m) => s"model ${n.value} of ${m.value}"

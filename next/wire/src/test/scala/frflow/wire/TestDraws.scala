package frflow.wire

import frflow.core.example.Given
import frflow.core.expr.{Side, Value}
import frflow.core.name.{BoundaryName, CtorName, DefName, ModelName, NodeId, OpName, SymbolName, TypeName}
import frflow.core.ty.{NumKind, Ty}
import frflow.eval.{EvalError, ScalaValue}
import frflow.eval.run.Broken
import frflow.testing.Seed
import frflow.testing.model.{Difference, Step}
import frflow.testing.report.{Against, Drawn, Failure, Made, Position, TestReport}
import frflow.wire.Draws.*
import org.scalacheck.{Arbitrary, Gen}

/** Test reports and failing cases: every type, value, error and failure. A model test's Scala values are drawn as
  * texts, the only Scala values the file keeps as they were.
  */
object TestDraws:
  private val small = Gen.choose(0, 12)

  def ty(depth: Int): Gen[Ty] =
    val leaf = Gen.oneOf(Gen.oneOf(Ty.Bool, Ty.Str, Ty.Unit, Ty.World, Ty.Never),
      Gen.oneOf(NumKind.values.toList).map(Ty.Num(_)), word.map(n => Ty.Sort(TypeName(n))),
      word.map(n => Ty.Data(TypeName(n))))
    if depth == 0 then leaf else
      val t = ty(depth - 1)
      Gen.oneOf(leaf, t.map(Ty.ListOf(_)), t.map(Ty.OptionOf(_)), Gen.zip(t, t).map(Ty.EitherOf(_, _)),
        Gen.zip(t, t).map(Ty.MapOf(_, _)), t.map(Ty.SetOf(_)), few(t).map(Ty.TupleOf(_)),
        Gen.zip(few(t), t).map(Ty.FnOf(_, _)), Gen.zip(t, Gen.option(t)).map(Ty.FlowOf(_, _)))

  def value(depth: Int): Gen[Value] =
    val leaf = Gen.oneOf(Gen.oneOf(true, false).map(Value.Bool(_)), Arbitrary.arbitrary[BigInt].map(Value.Num(_)),
      text.map(Value.Str(_)), Gen.const(Value.Unit))
    if depth == 0 then leaf else
      val v = value(depth - 1)
      Gen.oneOf(leaf, Gen.zip(word, few(v)).map((c, fs) => Value.Data(CtorName(c), fs)), few(v).map(Value.Many(_)),
        Gen.option(v).map(Value.Maybe(_)), few(Gen.zip(v, v)).map(Value.Pairs(_)), few(v).map(Value.Tuple(_)),
        Gen.zip(Gen.oneOf(Side.values.toList), v).map(Value.Inject(_, _)),
        Gen.zip(few(Gen.zip(word.map(ModelName(_)), v)), few(Gen.oneOf(true, false))).map(Value.World(_, _)))

  val evalError: Gen[EvalError] = Gen.oneOf(Gen.oneOf(EvalError.Quantified, EvalError.NoCase, EvalError.Steps),
    word.map(s => EvalError.Unbound(SymbolName(s))), word.map(d => EvalError.NoDefine(DefName(d))),
    word.map(m => EvalError.NoModel(ModelName(m))))

  val broken: Gen[Broken] = Gen.oneOf(Gen.const(Broken.Post), node.map(Broken.Always(_)),
    node.map(Broken.Assumption(_)), evalError.map(Broken.NotEvaluated(_)), text.map(Broken.Threw(_)))

  val drawn: Gen[Drawn] = Gen.zip(Arbitrary.arbitrary[Long].map(Seed(_)), small, small).map(Drawn(_, _, _))
  private val scala: Gen[ScalaValue] = text.map(ScalaValue(_))
  val step: Gen[Step] =
    Gen.zip(word, word, few(scala)).map((b, o, args) => Step(BoundaryName(b), OpName(o), args))

  val difference: Gen[Difference] = Gen.oneOf(Gen.zip(step, scala, scala).map(Difference.Answer(_, _, _)),
    Gen.zip(scala, scala).map(Difference.State(_, _)), text.map(Difference.Threw(_)))

  val failure: Gen[Failure] = Gen.oneOf(
    Gen.zip(few(value(2)), few(Gen.zip(word.map(SymbolName(_)), value(1)).map(Given(_, _))), broken, drawn)
      .map(Failure.Call(_, _, _, _)),
    Gen.zip(value(2), few(step), difference, drawn).map(Failure.Run(_, _, _, _)))

  val against: Gen[Against] = Gen.oneOf(node.map(Against.Claim(_)), word.map(d => Against.Define(DefName(d))),
    Gen.zip(node, small).map(Against.Model(_, _)))

  val report: Gen[TestReport] = Gen.zip(small, Arbitrary.arbitrary[Long].map(Seed(_)), against, Gen.option(failure),
    few(small.map(Position(_))), few(Gen.zip(ty(2), Gen.option(text)).map(Made(_, _))))
    .map(TestReport(_, _, _, _, _, _))

  val tests: Gen[Map[NodeId, (String, TestReport)]] = byKey(node, Gen.zip(hex, report))
  val counterexamples: Gen[Map[NodeId, List[Failure]]] = byKey(node, few(failure))

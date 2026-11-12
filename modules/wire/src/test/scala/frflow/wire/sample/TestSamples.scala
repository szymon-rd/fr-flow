package frflow.wire.sample

import frflow.core.example.Given
import frflow.core.expr.{Side, Value}
import frflow.core.name.{CtorName, NodeId, SymbolName, TypeName}
import frflow.core.ty.{NumKind, Ty}
import frflow.eval.EvalError
import frflow.eval.run.Broken
import frflow.testing.report.{Count, Drawn, Failure, Made, Note, Outcome, Position, Reach, Seed, Target,
  TestReport}

/** The golden tests and counterexamples: a call that broke its claim. */
object TestSamples:
  private def booking(room: String, from: Int, to: Int) =
    Value.Data(CtorName("mk"), List(Value.Str(room), Value.Num(from), Value.Num(to)))

  private val call = Failure(List(Value.Many(List(booking("Oak", 9, 10))), booking("Oak", 9, 11)),
    List(Given(SymbolName("rooms"), Value.Pairs(List(Value.Str("Oak") -> Value.Maybe(Some(Value.Num(4))))))),
    Broken.Always(NodeId("NoOverlap")), Drawn(Seed(42), 17, 3))

  private val failed = TestReport(Count(500, 18), Seed(42), NodeId("Book"), Outcome.Failed(call),
    List(Target(Position(List(1)), Reach.Premise), Target(Position(List(0, 2)), Reach.Arm(1))),
    List(Note.Given(Made(Ty.ListOf(Ty.Data(TypeName("Booking"))), Some("bookings on one day"))),
      Note.Given(Made(Ty.MapOf(Ty.Str, Ty.Num(NumKind.Int32)), None)),
      Note.NeverMade(Ty.Data(TypeName("Booking")), List(booking("Elm", 0, 1)))))

  private val passed = TestReport(Count(100, 100), Seed(1), NodeId("Free"),
    Outcome.NotChecked(EvalError.Quantified), Nil, List(Note.Given(Made(Ty.TupleOf(
    List(Ty.EitherOf(Ty.Bool, Ty.Unit), Ty.OptionOf(Ty.SetOf(Ty.Str)), Ty.FnOf(List(Ty.Unit), Ty.Str))), None)),
    Note.NothingToVary))

  val tests: Map[NodeId, (String, TestReport)] = Map(NodeId("Book") -> ("a1b2c3", failed),
    NodeId("Free") -> ("070809", passed))

  private val threw = Failure(List(Value.Tuple(List(Value.Unit, Value.Bool(true))),
    Value.Inject(Side.Error, Value.Str("full"))), Nil, Broken.NotEvaluated(EvalError.Unbound(SymbolName("now"))),
    Drawn(Seed(3), 0, 1))

  val counterexamples: Map[NodeId, List[Failure]] = Map(NodeId("Book") -> List(call, threw))

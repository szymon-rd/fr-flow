package frflow.wire.sample

import frflow.core.example.Given
import frflow.core.expr.{Side, Value}
import frflow.core.name.{BoundaryName, CtorName, ModelName, NodeId, OpName, SymbolName, TypeName}
import frflow.core.ty.{NumKind, Ty}
import frflow.eval.EvalError
import frflow.eval.run.Broken
import frflow.testing.Seed
import frflow.testing.model.{Difference, Ran, Step}
import frflow.testing.report.{Against, Count, Drawn, Failure, Made, Note, Outcome, Position, Reach, Target,
  TestReport}

/** The golden tests and counterexamples: a call that broke its claim, a model run its store answered differently. */
object TestSamples:
  private def booking(room: String, from: Int, to: Int) =
    Value.Data(CtorName("mk"), List(Value.Str(room), Value.Num(from), Value.Num(to)))

  private val call = Failure.Call(List(Value.Many(List(booking("Oak", 9, 10))), booking("Oak", 9, 11)),
    List(Given(SymbolName("rooms"), Value.Pairs(List(Value.Str("Oak") -> Value.Maybe(Some(Value.Num(4))))))),
    Broken.Always(NodeId("NoOverlap")), Drawn(Seed(42), 17, 3))

  private def run(d: Difference) = Failure.Run(Value.World(List(ModelName("stored") -> Value.Many(Nil)),
    List(false, true)), List(Step(BoundaryName("Bookings"), OpName("add"), List(booking("Oak", 9, 10)))),
    d, Drawn(Seed(-7), 2, 1))
  private val answered = run(Difference.Call(Step(BoundaryName("Bookings"), OpName("list"), Nil),
    Ran.Gave(Value.Many(Nil)), Ran.Gave(Value.Many(List(booking("Oak", 9, 10))))))

  private val failed = TestReport(Count(500, 18), Seed(42), Against.Claim(NodeId("Book")), Outcome.Failed(call),
    List(Target(Position(List(1)), Reach.Premise), Target(Position(List(0, 2)), Reach.Arm(1))),
    List(Note.Given(Made(Ty.ListOf(Ty.Data(TypeName("Booking"))), Some("bookings on one day"))),
      Note.Given(Made(Ty.MapOf(Ty.Str, Ty.Num(NumKind.Int32)), None)),
      Note.NeverMade(Ty.Data(TypeName("Booking")), List(booking("Elm", 0, 1)))))

  private val modelled = TestReport(Count(200, 3), Seed(-7), Against.Model(NodeId("Store"), 0),
    Outcome.Failed(answered), List(Target(Position(List(1)), Reach.Called(OpName("remove")))),
    List(Note.Given(Made(Ty.FlowOf(Ty.Unit, Some(Ty.Sort(TypeName("Fault")))), None))))

  private val passed = TestReport(Count(100, 100), Seed(1), Against.Claim(NodeId("Free")),
    Outcome.NotChecked(EvalError.Quantified), Nil, List(Note.Given(Made(Ty.TupleOf(
    List(Ty.EitherOf(Ty.Bool, Ty.Unit), Ty.OptionOf(Ty.SetOf(Ty.World)), Ty.FnOf(List(Ty.Never), Ty.Str))), None)),
    Note.NothingToVary))

  val tests: Map[NodeId, (String, TestReport)] = Map(NodeId("Book") -> ("a1b2c3", failed),
    NodeId("Store") -> ("d4e5f6", modelled), NodeId("Free") -> ("070809", passed))

  private val threw = Failure.Call(List(Value.Tuple(List(Value.Unit, Value.Bool(true))),
    Value.Inject(Side.Error, Value.Str("full"))), Nil, Broken.NotEvaluated(EvalError.Unbound(SymbolName("now"))),
    Drawn(Seed(3), 0, 1))

  val counterexamples: Map[NodeId, List[Failure]] = Map(NodeId("Book") -> List(call, threw),
    NodeId("Store") -> List(run(Difference.State(Value.Many(Nil), Value.Many(List(Value.Str("x"))))),
      run(Difference.Call(Step(BoundaryName("Bookings"), OpName("add"), Nil), Ran.Threw("closed"),
        Ran.Failed(Value.Str("down")))), run(Difference.NotRun("closed"))))

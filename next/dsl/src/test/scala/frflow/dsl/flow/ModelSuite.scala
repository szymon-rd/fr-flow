package frflow.dsl.flow

import frflow.core.expr.{Binder, Prog, Progs}
import frflow.core.name.{ModelName, SymbolName, VarId}
import frflow.core.ty.{NumKind, Ty}
import frflow.core.vocab.StateModel as Read
import frflow.dsl.model.Clock
import frflow.core.term.interpret.ToExpr
import frflow.dsl.term.{Notes, Term}

/** A model of a state read from its object: named as the object, each operation's meaning its steps over the state
  * from its parameters, named as written; the clock's model, FrFlow's own, declared by any mention of its operations.
  */
class ModelSuite extends munit.FunSuite:
  private def read(m: frflow.dsl.model.StateModel[?]): Read =
    m.model.run.fold(e => fail(e.toString), _._2)
  private def steps(m: Read): List[(String, List[String], String)] = m.ops.map(o =>
    (o.op.value, o.params.map(_.hint), Progs.all(Progs.map(o.steps)(s => ToExpr.of(s.run, 1)))
      .collect { case Prog.Read(_) => "get"; case Prog.Write(_, _) => "set" }.mkString(", ")))

  test("a model named as its object: each operation's steps over its state, in the order given") {
    val kept = read(Store.kept)
    assertEquals((kept.name, kept.state, kept.fails), (ModelName("kept"), Ty.Num(NumKind.Big), None))
    assertEquals(steps(kept), List(("load", Nil, "get"), ("save", List("n"), "set")))
    assertEquals(kept.ops.map(_.result), List(Ty.Num(NumKind.Big), Ty.Unit))
  }

  test("the clock's model: the time now read, a sleep adding its seconds") {
    val clock = read(Clock.clockModel)
    assertEquals(clock.name, ModelName("clockModel"))
    assertEquals(steps(clock), List(("now", Nil, "get"), ("sleep", List("seconds"), "get, set")))
    clock.op(SymbolName("sleep")).map(_.steps) match
      case Some(Prog.Bind(Prog.Read(_), _, Prog.Bind(Prog.Write(_, _), _, Prog.Pure(_)))) => ()
      case other                                                                         => fail(other.toString)
  }

  test("a mention of a clock's operation declares the clock's model, so a program calling it has its state") {
    assertEquals(Notes.in(Clock.now).declares.models.keySet, Set(ModelName("clockModel")))
    assertEquals(Notes.in(Clock.sleep).declares.models.keySet, Set(ModelName("clockModel")))
    val now = Term.free[frflow.core.term.World](Binder(VarId.level(0), "w", Ty.World))
    assertEquals(Notes.in(Store.kept.in(now)).declares.symbols.keySet, Set(SymbolName("load"), SymbolName("save")))
  }

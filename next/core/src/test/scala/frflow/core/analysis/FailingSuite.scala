package frflow.core.analysis

import frflow.core.{Booking, Lang, Store}
import frflow.core.Nodes.*
import frflow.core.expr.{Binder, Expr, Prog, Progs, Value}
import frflow.core.name.{BoundaryName, NodeId, OpName, SymbolName, VarId}
import frflow.core.ty.Ty
import frflow.core.vocab.SymbolType

/** A program's error, read off its steps (`Progs.failsWith`) and put in its type (`Failing.typed`, by `Resolve`); and
  * the parts `impl` may rest on: any, a part about the node's own Definition too.
  */
class FailingSuite extends munit.FunSuite:
  private val (store, mail) = (BoundaryName("Store"), BoundaryName("Mail"))
  private val failing: BoundaryName => Option[Ty] = Map(store -> Ty.Str).get
  private val call = Prog.Call[Expr](store, OpName("load"), Nil, Ty.Unit)
  private val mailed = Prog.Call[Expr](mail, OpName("send"), Nil, Ty.Unit)
  private val raise = Prog.Raise[Expr](Expr.Lit(Value.Num(1), Lang.big))
  private val x = Binder(VarId.step(0), "x", Ty.Unit)
  private def caught(p: Prog[Expr], t: Ty) =
    Prog.Catch(p, t, Binder(VarId.step(1), "e", t), Prog.Pure(Expr.Lit(Value.Unit, Ty.Unit)))

  test("a program fails with what it raises and with its failing boundaries' errors, outside a handler of them") {
    assertEquals(List(call, mailed, raise, Prog.Bind(call, x, raise)).map(Progs.failsWith(_, failing)),
      List(List(Ty.Str), Nil, List(Lang.big), List(Ty.Str, Lang.big)))
    assertEquals(List(caught(call, Ty.Str), caught(raise, Lang.big), caught(Prog.Bind(call, x, raise), Ty.Str))
      .map(Progs.failsWith(_, failing)), List(Nil, Nil, List(Lang.big)))
  }

  test("a handler's own steps are outside it: what the handler raises is not caught") {
    val rethrows = Prog.Catch(call, Ty.Str, Binder(VarId.step(1), "e", Ty.Str), raise)
    assertEquals(Progs.failsWith(rethrows, failing), List(Lang.big))
  }

  test("resolved, a program's type and its Definition's carry its error: the store's when it may be down") {
    val types = List(Store.kb, FailureCases.down).map(kb => Resolve(Validate(kb.elaborated).toOption.get).theory)
      .map(t => (t.vocabulary.symbol(Store.book).map(_.ty), t.vocabulary.defines.map(_.lambda.result)))
    assertEquals(types, List(
      (Some(SymbolType.Typed(Ty.FnOf(List(Booking.ty), Ty.FlowOf(Ty.Unit, None)))), List(Ty.FlowOf(Ty.Unit, None))),
      (Some(SymbolType.Typed(Ty.FnOf(List(Booking.ty), Ty.FlowOf(Ty.Unit, Some(Ty.Str))))),
        List(Ty.FlowOf(Ty.Unit, Some(Ty.Str))))))
  }

  test("a part of a node proven of code may be about the node's own Definition: impl rests on it, the code in it") {
    val own = ValueCases.proven.without("stray").and(ValueCases.holdsOf("grantedToo", "granted"))
      .linking(partOf("grantedToo", "top"))
    assertEquals((own.problems, ValueCases.proven.problems), (Nil, Nil))
    assertEquals(Constrained.of(own.theory, NodeId("grantedToo")), List(SymbolName("granted")))
  }

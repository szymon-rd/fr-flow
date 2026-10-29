package frflow.core.analysis

import frflow.core.{Booking, Failing, Lang, Store}
import frflow.core.Nodes.*
import frflow.core.expr.{Binder, Expr, Exprs, Prog, Progs, Value}
import frflow.core.name.{DefName, NodeId, SourceText, SymbolName, VarId}
import frflow.core.spec.{Form, Written}
import frflow.core.term.{Stated, Sym}
import frflow.core.ty.Ty
import frflow.core.vocab.{Define, DefineForm, SymbolType}

/** A program's error, read off its steps (`Progs.failsWith`) and put in its type (`Failing.typed`, by `Resolve`); and
  * the parts `impl` may rest on: any, a part about the node's own Definition too.
  */
class FailingSuite extends munit.FunSuite:
  private val (load, send) = (SymbolName("load"), SymbolName("send"))
  private val failing: SymbolName => Option[Ty] = Map(load -> Ty.Str).get
  private val call = Prog.Call[Expr](load, Nil, Ty.Unit)
  private val mailed = Prog.Call[Expr](send, Nil, Ty.Unit)
  private val raise = Prog.Raise[Expr](Expr.Lit(Value.Num(1), Lang.big))
  private val x = Binder(VarId.step(0), "x", Ty.Unit)
  private def caught(p: Prog[Expr], t: Ty) =
    Prog.Catch(p, t, Binder(VarId.step(1), "e", t), Prog.Pure(Expr.Lit(Value.Unit, Ty.Unit)))

  test("a program fails with what it raises and with its failing models' errors, outside a handler of them") {
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

  test("the monad's error is every error raised, handled or met; what escapes, those outside a handler of them") {
    val v = FailureCases.down.theory.vocabulary
    def define(p: Prog[Stated[?]]) = Define(DefName("p"), Written.steps(Nil, p, Ty.Unit, SourceText("p")),
      DefineForm.Flow)
    val handled = Prog.Catch[Stated[?]](Prog.Call(Store.add, Nil, Ty.Unit), Ty.Str,
      Binder(VarId.step(1), "e", Ty.Str), Prog.Pure(Stated([T[_]] => (s: Sym[T]) => s.bool(true))))
    assertEquals((Failing.of(v, define(handled)), Failing.escaping(v, define(handled))), (List(Ty.Str), Nil))
    val thenRaising = define(Prog.Bind(handled, x, Prog.Raise(Stated([T[_]] => (s: Sym[T]) => Lang(s).num(1)))))
    // Handling the store's string and failing with a number would need two monads: `ErrorsDiffer`.
    assertEquals((Failing.of(v, thenRaising), Failing.escaping(v, thenRaising)), (List(Ty.Str, Lang.big),
      List(Lang.big)))
  }

  test("a program handling every error it meets runs over it, and a failing run's clause on it is refused") {
    val careful = FailureCases.down.declaring(v => v.copy(defines = v.defines.map(d => d.copy(written =
      Written.steps(d.lambda.params, Prog.Catch(steps(d), Ty.Str, Binder(VarId.step(1), "e", Ty.Str),
        Prog.Pure(Stated([T[_]] => (s: Sym[T]) => s.bool(true)))), Ty.Unit, d.written.source)))))
    val r = Resolve(Validate(careful.elaborated).toOption.get)
    assertEquals(r.theory.vocabulary.symbol(Store.book).map(_.ty),
      Some(SymbolType.Typed(Ty.FnOf(List(Booking.ty), Ty.FlowOf(Ty.Unit, Some(Ty.Str))))))
    assertEquals(FailureCases.claiming(careful, Ty.Str).problems,
      List(Problem.NeverFails(NodeId("bookFails"), Store.book)))
  }

  test("resolved, a formula's IR says a program's type as its code gives it, its error too") {
    val r = Resolve(Validate(FailureCases.claiming(FailureCases.down, Ty.Str).elaborated).toOption.get)
    val said = r.theory.node(NodeId("bookFails")).flatMap(_.statement.said).toList.flatMap(f => Exprs.all(f.value))
    assertEquals(said.collect { case Expr.Sym(Store.book, ty) => ty }.distinct,
      List(Ty.FnOf(List(Booking.ty), Ty.FlowOf(Ty.Unit, Some(Ty.Str)))))
  }

  private def steps(d: Define): Prog[Stated[?]] = d.written.form match
    case Form.Steps(p) => p
    case Form.Term(_)  => fail("the store's program has steps")

  test("a part of a node proven of code may be about the node's own Definition: impl rests on it, the code in it") {
    val own = ValueCases.proven.without("stray").and(ValueCases.holdsOf("grantedToo", "granted"))
      .linking(partOf("grantedToo", "top"))
    assertEquals((own.problems, ValueCases.proven.problems), (Nil, Nil))
    assertEquals(Constrained.of(own.theory, NodeId("grantedToo")), List(SymbolName("granted")))
  }

package frflow.core.analysis

import frflow.core.{Booking, Store}
import frflow.core.expr.{Binder, Expr, Prog, Value}
import frflow.core.name.{ModelName, SymbolName, VarId}
import frflow.core.term.{Stated, Sym}
import frflow.core.ty.Ty
import frflow.core.vocab.{ModelOp, StateModel}

/** Which steps of two sides at once are asked to commute (`AtOnce.pairs`): two calls on a model in common, a call
  * beside each call inside a transaction of the other side (it may come between them), two transactions whole; of a
  * traverse, each pair once; nothing of steps on models apart.
  */
class AtOnceSuite extends munit.FunSuite:
  private val (b, c) = (Binder(VarId.level(0), "b", Booking.ty), Binder(VarId.level(1), "c", Booking.ty))
  private val apart = ModelName("apart")
  private val put = SymbolName("put")
  private val v = Store.kb.vocabulary.copy(models = Store.kb.vocabulary.models :+
    StateModel(apart, "another store", Ty.Unit, List(ModelOp(put, Nil, Ty.Unit,
      Prog.Pure(Stated([T[_]] => (s: Sym[T]) => s.lit((), Value.Unit, Ty.Unit))))), None))
  private def add(x: Binder): Prog[Expr] = Prog.Call(Store.add, List(Expr.Var(x)), Ty.Unit)
  private def call(op: SymbolName): Prog[Expr] = Prog.Call(op, Nil, Ty.Unit)
  private val (u, w) = (Binder(VarId.step(0), "u", Ty.Unit), Binder(VarId.step(1), "w", Ty.Unit))
  private def both(l: Prog[Expr], r: Prog[Expr]): Prog[Expr] = Prog.Par(l, u, r, w)
  private val twoAdds = Prog.Atomic(Prog.Bind(add(b), Binder(VarId.step(2), "_$u", Ty.Unit), add(c)))

  test("two calls on a model in common: one pair; on models apart, none") {
    assertEquals(AtOnce.pairs(v, both(add(b), add(c))), List(0 -> 0))
    assertEquals(AtOnce.pairs(v, both(add(b), call(put))), Nil)
  }

  test("a call beside a transaction: beside each call inside it, not beside the whole") {
    assertEquals(AtOnce.units(twoAdds), List(twoAdds, add(b), add(c)))
    assertEquals(AtOnce.pairs(v, both(twoAdds, add(b))), List(1 -> 0, 2 -> 0))
  }

  test("two transactions: whole, one pair") {
    assertEquals(AtOnce.pairs(v, both(twoAdds, twoAdds)), List(0 -> 0))
  }

  test("a traverse at once: its body beside itself, each pair once; a race's sides as written") {
    val each = Prog.ParEach(Expr.Var(Binder(VarId.level(2), "xs", Ty.ListOf(Booking.ty))), b,
      Prog.Bind(add(b), Binder(VarId.step(3), "_$u", Ty.Unit), add(c)), None)
    assertEquals(AtOnce.pairs(v, each), List(0 -> 0, 0 -> 1, 1 -> 1))
    assertEquals(AtOnce.pairs(v, Prog.Race(add(b), add(c), Prog.Pure(Expr.Var(b)))), List(0 -> 0))
    assertEquals(AtOnce.all(v, Prog.Bind(both(add(b), add(c)), Binder(VarId.step(4), "p", Ty.Unit), each)).map(_._1),
      List(0, 1, 1, 1))
  }

  test("a race is a concurrent step of the program, its sides' pairs asked, nested in a pair too") {
    val race = Prog.Race(add(b), add(c), Prog.Pure(Expr.Var(b)))
    assertEquals(AtOnce.all(v, race), List(0 -> (0 -> 0)))
    assertEquals(AtOnce.all(v, both(race, call(put))), List(1 -> (0 -> 0)))
  }

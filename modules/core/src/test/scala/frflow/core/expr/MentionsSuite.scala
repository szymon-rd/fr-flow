package frflow.core.expr

import cats.kernel.{Eq, Monoid}
import cats.kernel.laws.discipline.MonoidTests
import cats.syntax.all.*
import frflow.core.{Booking, Lang}
import frflow.core.name.{DefName, ModelName, SymbolName, TypeName, VarId}
import frflow.core.term.interpret.ToExpr
import frflow.core.ty.Ty
import org.scalacheck.{Arbitrary, Gen}

/** The laws of `Mentions`: a monoid on values holding each name once, combining keeps the order first met; and
  * `Exprs.mentions`, which says exactly what a term names, gathered from its parts.
  */
class MentionsSuite extends munit.DisciplineSuite:
  private def names[A](pool: String*)(f: String => A): Gen[List[A]] =
    Gen.listOf(Gen.oneOf(pool)).map(_.distinct.map(f))
  private given Arbitrary[Mentions] = Arbitrary(for
    s <- names("a", "b", "c")(SymbolName(_)); d <- names("d", "e")(DefName(_)); t <- names("T", "U")(TypeName(_))
    o <- names("add", "load")(SymbolName(_)); m <- names("m", "n")(ModelName(_))
  yield Mentions(s, d, t, o, m))
  private given Eq[Mentions] = Eq.fromUniversalEquals

  checkAll("Mentions", MonoidTests[Mentions].monoid)

  test("combining keeps each name once, in the order first met") {
    val (a, b) = (Mentions(List(SymbolName("a")), Nil, Nil, Nil, List(ModelName("m"))),
      Mentions(List(SymbolName("b"), SymbolName("a")), Nil, Nil, Nil, List(ModelName("n"), ModelName("m"))))
    assertEquals(a |+| b, Mentions(List(SymbolName("a"), SymbolName("b")), Nil, Nil, Nil,
      List(ModelName("m"), ModelName("n"))))
    assertEquals(Monoid[Mentions].empty, Mentions.empty)
  }

  test("a term mentions exactly the symbols, defines, types and models it is built from, in the order met") {
    (1L to 300L).foreach { seed =>
      val g = Terms(seed)
      val e = ToExpr.of(Tm.closed(g.bool(3, 0)))
      assertEquals(Exprs.mentions(e), g.mentioned, e)
    }
  }

  test("what an expression mentions includes what each of its parts mentions") {
    (1L to 300L).map(seed => ToExpr.of(Tm.closed(Terms(seed).bool(3, 0)))).foreach { e =>
      Exprs.all(e).foreach(x => assertEquals(Exprs.children(x).foldMap(Exprs.mentions) |+| Exprs.mentions(x),
        Exprs.mentions(x), x))
    }
  }

  test("a node naming nothing itself mentions what its parts do, combined in order") {
    val parts = (1L to 50L).map(seed => ToExpr.of(Tm.closed(Terms(seed).bool(2, 0)))).toList
    parts.sliding(3).foreach { es =>
      assertEquals(Exprs.mentions(Expr.Tuple(es)), es.foldMap(Exprs.mentions))
      assertEquals(Exprs.mentions(Expr.Prim(PrimOp.And, es.take(2), Ty.Bool)), es.take(2).foldMap(Exprs.mentions))
    }
  }

  test("each leaf names what it is about: a symbol, a define, a model's state, a program's operations, the outside") {
    val (m, add, book) = (ModelName("stored"), SymbolName("add"), SymbolName("book"))
    val w = Expr.Var(Binder(VarId.level(0), "w", Ty.World))
    val call = Prog.Call(add, Nil, Ty.Unit)
    assertEquals(Exprs.mentions(Expr.Sym(book, Booking.ty)), Mentions(List(book), Nil, List(Booking.name), Nil, Nil))
    assertEquals(Exprs.mentions(Expr.Call(DefName("d"), Nil, Ty.Bool)), Mentions(Nil, List(DefName("d")), Nil, Nil,
      Nil))
    assertEquals(Exprs.mentions(Expr.Part(w, m, Ty.ListOf(Booking.ty))), Mentions(Nil, Nil, List(Booking.name), Nil,
      List(m)))
    assertEquals(Exprs.mentions(Expr.Do(Prog.Bind(call, Binder(VarId.step(0), "u", Ty.Unit), Prog.Read(m)),
      Ty.FlowOf(Ty.Unit, None))), Mentions(Nil, Nil, Nil, List(add), List(m)))
    assertEquals(Exprs.mentions(Expr.Outside(OutsideFact.Atomic(m))), Mentions(Nil, Nil, Nil, Nil, List(m)))
    assertEquals(Exprs.mentions(Expr.Outside(OutsideFact.OnlyCodeChanges(m))), Mentions(Nil, Nil, Nil, Nil, List(m)))
    assertEquals(Exprs.mentions(Expr.Outside(OutsideFact.Initially(m, DefName("empty")))),
      Mentions(Nil, List(DefName("empty")), Nil, Nil, List(m)))
  }

  test("a binder mentions its variable's type") {
    val x = Binder(VarId.level(0), "b", Booking.ty)
    assertEquals(Exprs.mentions(Expr.Quant(Quantifier.Forall, List(x), Expr.Lit(Value.Bool(true), Ty.Bool))),
      Mentions(Nil, Nil, List(Booking.name), Nil, Nil))
    assertEquals(Exprs.mentions(Expr.Lit(Value.Num(1), Lang.big)), Mentions.empty)
  }

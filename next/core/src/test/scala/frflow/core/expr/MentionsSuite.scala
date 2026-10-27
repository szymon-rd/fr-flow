package frflow.core.expr

import cats.kernel.Monoid
import cats.syntax.all.*
import frflow.core.{Booking, Lang}
import frflow.core.name.{BoundaryName, DefName, ModelName, OpName, SymbolName, TypeName, VarId}
import frflow.core.term.interpret.ToExpr
import frflow.core.ty.Ty
import scala.util.Random

/** The laws of `Mentions`: a monoid that keeps each name once, in the order first met; and `Exprs.mentions`, which
  * says exactly what a term names, gathered from its parts.
  */
class MentionsSuite extends munit.FunSuite:
  private def pick[A](r: Random, pool: List[A]): List[A] = List.fill(r.nextInt(4))(pool(r.nextInt(pool.size)))
  private def mentions(seed: Long): Mentions =
    val r = Random(seed)
    Mentions(pick(r, List("a", "b", "c").map(SymbolName(_))), pick(r, List("d", "e").map(DefName(_))),
      pick(r, List("T", "U").map(TypeName(_))), pick(r, List("B").map(BoundaryName(_))),
      pick(r, List("m", "n").map(ModelName(_))))
  private val values = (1L to 200L).map(mentions).toList
  private val triples = values.zip(values.drop(1)).zip(values.drop(2)).map { case ((a, b), c) => (a, b, c) }
  private val empty = Monoid[Mentions].empty

  test("the empty mentions are an identity: on either side, each name once") {
    values.foreach(m => assertEquals((empty |+| m, m |+| empty), (m |+| m, m |+| m)))
    values.foreach(m => assertEquals(empty |+| (empty |+| m), empty |+| m))
  }

  test("combining is associative") {
    triples.foreach((a, b, c) => assertEquals((a |+| b) |+| c, a |+| (b |+| c)))
  }

  test("combining is idempotent, and keeps each name once, in the order first met") {
    triples.foreach { (a, b, _) =>
      val ab = a |+| b
      assertEquals(ab |+| ab, ab)
      assertEquals(ab.symbols, (a.symbols ++ b.symbols).distinct)
      assertEquals(ab.models, (a.models ++ b.models).distinct)
    }
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

  test("each leaf names what it is about: a symbol, a define, a model's state, a program's store, the outside") {
    val (m, b, book) = (ModelName("stored"), BoundaryName("Bookings"), SymbolName("book"))
    val w = Expr.Var(Binder(VarId.level(0), "w", Ty.World))
    val call = Prog.Call(b, OpName("add"), Nil, Ty.Unit)
    assertEquals(Exprs.mentions(Expr.Sym(book, Booking.ty)), Mentions(List(book), Nil, List(Booking.name), Nil, Nil))
    assertEquals(Exprs.mentions(Expr.Call(DefName("d"), Nil, Ty.Bool)), Mentions(Nil, List(DefName("d")), Nil, Nil,
      Nil))
    assertEquals(Exprs.mentions(Expr.Part(w, m, Ty.ListOf(Booking.ty))), Mentions(Nil, Nil, List(Booking.name), Nil,
      List(m)))
    assertEquals(Exprs.mentions(Expr.Do(Prog.Bind(call, Binder(VarId.step(0), "u", Ty.Unit), Prog.Read(m)),
      Ty.FlowOf(Ty.Unit))), Mentions(Nil, Nil, Nil, List(b), List(m)))
    assertEquals(Exprs.mentions(Expr.Outside(OutsideFact.WrittenOnlyBy(m, List(book)))),
      Mentions(List(book), Nil, Nil, Nil, List(m)))
    assertEquals(Exprs.mentions(Expr.Outside(OutsideFact.BehavesAs(b, m))), Mentions(Nil, Nil, Nil, List(b), List(m)))
    assertEquals(Exprs.mentions(Expr.Outside(OutsideFact.Initially(m, DefName("empty")))),
      Mentions(Nil, List(DefName("empty")), Nil, Nil, List(m)))
    assertEquals(Exprs.mentions(Expr.Outside(OutsideFact.Calls(book))), Mentions(List(book), Nil, Nil, Nil, Nil))
  }

  test("a binder mentions its variable's type") {
    val x = Binder(VarId.level(0), "b", Booking.ty)
    assertEquals(Exprs.mentions(Expr.Quant(Quantifier.Forall, List(x), Expr.Lit(Value.Bool(true), Ty.Bool))),
      Mentions(Nil, Nil, List(Booking.name), Nil, Nil))
    assertEquals(Exprs.mentions(Expr.Lit(Value.Num(1), Lang.big)), Mentions.empty)
  }

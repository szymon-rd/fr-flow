package frflow.core.expr

import frflow.core.{Booking, Lang}
import frflow.core.name.{ModelName, SourceText, SymbolName, VarId}
import frflow.core.spec.Written
import frflow.core.term.interpret.ToExpr
import frflow.core.ty.Ty

/** The laws of `Exprs.typeOf` on generated terms of every sort: the IR of a term is typed as the term is, and every
  * node of it as its parts are; and the type of each case of `Expr`.
  */
class TypeOfSuite extends munit.FunSuite:
  private val typing = Typing(n => if n == Booking.name then Booking.data.fieldTypes else Nil,
    d => Option.when(d == Terms.positive.name)(Terms.fnTy))
  private val seeds = (1L to 300L).toList

  /** Each sort's terms from each seed, with the type they are written at. */
  private val terms: List[(Expr, Ty)] = seeds.flatMap { seed =>
    val g = Terms(seed)
    List(ToExpr.of(Tm.closed(g.bool(3, 0))) -> Ty.Bool, ToExpr.of(Tm.closed(g.num(3, 0))) -> Lang.big,
      ToExpr.of(Tm.closed(g.nums(3, 0))) -> Ty.ListOf(Lang.big),
      ToExpr.of(Tm.closed(g.opt(3, 0))) -> Ty.OptionOf(Lang.big),
      ToExpr.of(Tm.closed(g.booking(3, 0))) -> Booking.ty, ToExpr.of(Tm.closed(g.fn(3, 0))) -> Terms.fnTy,
      ToExpr.of(Tm.closed(g.set(3, 0))) -> Ty.SetOf(Lang.big),
      ToExpr.of(Tm.closed(g.table(3, 0))) -> Ty.MapOf(Lang.big, Lang.big))
  }

  test("the IR of every term is typed as the term is written") {
    terms.foreach((e, t) => assertEquals(Exprs.typeOf(e), t, e))
  }

  test("every node of every term's IR is typed as its parts are") {
    terms.foreach((e, _) => assertEquals(typing.mistyped(e), Nil, e))
  }

  test("the generated terms reach every operation the laws are about") {
    val printed = terms.map(_._1.toString).mkString
    List("Quant(Forall", "Quant(Exists", "Iterate(Forall", "Iterate(Filter", "Pairwise(", "Fold(", "Let(", "If(",
      "Match(", "SomeP(", "Make(", "Copy(", "Field(", "Call(", "Apply(Sym", "Apply(Fun", "Fun(", "SomeOf(",
      "Nodup", "Cons", "Append", "Length", "Lit(Many", "Iterate(Map", "Iterate(FlatMap", "Iterate(Find", "Contains",
      "IsEmpty", "NonEmpty", "Zip", "Prim(Get,", "GetOrElse,", "GetOrElseAt", "Updated", "Incl", "Union", "Prod")
      .foreach(c => assert(printed.contains(c), c))
  }

  test("a written lambda's result is its body's type, over inputs bound at levels 0 … n-1") {
    val x = Binder(VarId.level(0), "x", Lang.big)
    (1L to 30L).foreach { seed =>
      val g = Terms(seed)
      val body = g.bool(2, 1)
      val w = Written.lambda(List(x), [T[_]] => (s: frflow.core.term.Sym[T]) =>
        body[T](s, Scope(List(s.free[BigInt](x)))), SourceText("…"))
      assertEquals((w.value.result, Exprs.typeOf(w.value.body)), (Ty.Bool, Ty.Bool))
      assertEquals(typing.mistyped(w.value.body), Nil)
    }
  }

  test("each case of Expr has the type its data says") {
    val (n, b) = (Expr.Lit(Value.Num(1), Lang.big), Expr.Lit(Value.Bool(true), Ty.Bool))
    val raise = Expr.Do(Prog.Raise(n), Ty.FlowOf(Ty.Never, None))
    val give = Expr.Do(Prog.Pure(n), Ty.FlowOf(Lang.big, None))
    val stop = Expr.Sym(SymbolName("stop"), Ty.Never)
    val x = Binder(VarId.level(0), "x", Lang.big)
    val w = Binder(VarId.level(1), "w", Ty.World)
    val store = Expr.Var(w)
    List(
      Expr.If(b, stop, n) -> Lang.big,
      Expr.If(b, n, stop) -> Lang.big,
      Expr.If(b, raise, give) -> Ty.FlowOf(Lang.big, None),
      Expr.If(b, give, raise) -> Ty.FlowOf(Lang.big, None),
      Expr.Fun(Lambda(List(x), b, Ty.Bool)) -> Terms.fnTy,
      Expr.Tuple(List(n, b)) -> Ty.TupleOf(List(Lang.big, Ty.Bool)),
      Expr.SomeOf(n) -> Ty.OptionOf(Lang.big),
      Expr.Inject(Side.Error, n, Ty.EitherOf(Lang.big, Ty.Bool)) -> Ty.EitherOf(Lang.big, Ty.Bool),
      Expr.Copy(Expr.Sym(SymbolName("slot"), Booking.ty), Booking.name, List(1 -> n)) -> Booking.ty,
      Expr.Make(Booking.name, Booking.make.ctor, Nil) -> Booking.ty,
      Expr.Fold(Expr.ListOf(Nil, Lang.big), n, x, x, n) -> Lang.big,
      Expr.Let(x, n, b) -> Ty.Bool,
      Expr.Pairwise(Expr.ListOf(Nil, Lang.big), x, x, b) -> Ty.Bool,
      Expr.Runs(Expr.Sym(SymbolName("book"), Ty.FlowOf(Ty.Unit, None)), store, false, x, w, b) -> Ty.Bool,
      Expr.Part(store, ModelName("stored"), Ty.ListOf(Booking.ty)) -> Ty.ListOf(Booking.ty),
      Expr.Do(Prog.Call(SymbolName("add"), Nil, Ty.Unit), Ty.FlowOf(Ty.Unit, None)) ->
        Ty.FlowOf(Ty.Unit, None),
      Expr.Outside(Terms.stored) -> Ty.Bool,
      Expr.Unchanged(store, store) -> Ty.Bool
    ).foreach((e, t) => assertEquals(Exprs.typeOf(e), t, e))
  }

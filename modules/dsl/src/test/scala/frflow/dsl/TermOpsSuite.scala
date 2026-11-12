package frflow.dsl

import frflow.core.expr.{Arm, Expr, Iteration, Pattern, PrimOp, Quantifier}
import frflow.core.term.Selector
import frflow.core.ty.{NumKind, Ty}
import frflow.dsl.term.*
import frflow.dsl.term.TermSyntax.*

/** The syntax of lists, options, maps, sets, pairs and eithers: each written as Scala writes it, each one operation of
  * the core's algebras, read by the analyses as the IR's (`ToExpr`).
  */
class TermOpsSuite extends munit.FunSuite:
  private val big = Ty.Num(NumKind.Big)
  private val xs: Term[List[BigInt]] = List(BigInt(1), BigInt(2))
  private val o: Term[Option[BigInt]] = Option(BigInt(3))
  private val m: Term[Map[BigInt, BigInt]] = Map(BigInt(1) -> BigInt(2))
  private val s: Term[Set[BigInt]] = Set(BigInt(1))
  private val one: Term[BigInt] = 1

  private def iterated(t: Term[?]): (Iteration, Ty) = t.expr match
    case Expr.Iterate(how, _, _, _, ty) => (how, ty)
    case other                          => fail(s"not an iteration: $other")

  private def prim(t: Term[?]): (PrimOp, Ty) = t.expr match
    case Expr.Prim(op, _, ty) => (op, ty)
    case other                => fail(s"not an operator: $other")

  /** The body of `forall(x => body)`. */
  private def body(t: Term[Boolean]): Expr = t.expr match
    case Expr.Quant(_, _, b) => b
    case other               => fail(s"not a quantifier: $other")

  test("a list's map, flatMap and find bind each element, typed by the body") {
    assertEquals(iterated(xs.map(x => x + one)), (Iteration.Map, Ty.ListOf(big)))
    assertEquals(iterated(xs.flatMap(x => x :: xs)), (Iteration.FlatMap, Ty.ListOf(big)))
    assertEquals(iterated(xs.find(x => one < x)), (Iteration.Find, Ty.OptionOf(big)))
  }

  test("a list's contains, isEmpty and zip are operators") {
    assertEquals(prim(xs.contains(one)), (PrimOp.Contains, Ty.Bool))
    assertEquals(prim(xs.isEmpty), (PrimOp.IsEmpty, Ty.Bool))
    assertEquals(prim(xs.zip(xs)), (PrimOp.Zip, Ty.ListOf(Ty.TupleOf(List(big, big)))))
  }

  test("an option's forall and exists bind the value it holds; isDefined and getOrElse are operators") {
    assertEquals(iterated(o.forall(x => one < x)), (Iteration.Forall, Ty.Bool))
    assertEquals(iterated(o.exists(x => one < x)), (Iteration.Exists, Ty.Bool))
    assertEquals(prim(o.isDefined), (PrimOp.NonEmpty, Ty.Bool))
    assertEquals(prim(o.getOrElse(one)), (PrimOp.GetOrElse, big))
  }

  test("a map's get, getOrElse and updated; a set's contains, incl and union") {
    assertEquals(prim(m.get(one)), (PrimOp.Get, Ty.OptionOf(big)))
    assertEquals(prim(m.getOrElse(one, one)), (PrimOp.GetOrElseAt, big))
    assertEquals(prim(m.updated(one, one)), (PrimOp.Updated, Ty.MapOf(big, big)))
    assertEquals(prim(s.contains(one)), (PrimOp.Contains, Ty.Bool))
    assertEquals(prim(s.incl(one)), (PrimOp.Incl, Ty.SetOf(big)))
    assertEquals(prim(s.union(s)), (PrimOp.Union, Ty.SetOf(big)))
  }

  test("a pair's _1 and _2 are its components, Lean's fields of Prod") {
    body(forall((p: Term[(BigInt, BigInt)]) => p._1 === p._2)) match
      case Expr.Prim(PrimOp.Eq, List(Expr.Field(_, a, 0, t), Expr.Field(_, b, 1, u)), _) =>
        assertEquals((a, b, t, u), (Selector.pair, Selector.pair, big, big))
      case other => fail(s"not two components: $other")
  }

  test("an Either's isRight and isLeft are matches on its sides") {
    List(forall((e: Term[Either[BigInt, BigInt]]) => e.isRight), forall((e: Term[Either[BigInt, BigInt]]) => e.isLeft))
      .map(body).foreach {
        case Expr.Match(_, arms, Ty.Bool) => assertEquals(arms.size, 2)
        case other                        => fail(s"not a match: $other")
      }
  }

  test("exists binds its variables as forall does, nested in order, each one's name kept") {
    exists((x: Term[BigInt]) => one < x).expr match
      case Expr.Quant(Quantifier.Exists, List(x), Expr.Prim(PrimOp.Lt, _, _)) =>
        assertEquals((x.hint, x.ty), ("x", big))
      case other => fail(s"not an exists: $other")
    exists((a: Term[BigInt], b: Term[Boolean]) => b && a === one).expr match
      case Expr.Quant(Quantifier.Exists, List(a), Expr.Quant(Quantifier.Exists, List(b), _)) =>
        assertEquals((a.hint, b.hint, b.ty), ("a", "b", Ty.Bool))
      case other => fail(s"not two exists: $other")
  }

  /** The fold an option's operation is: its arms, `none` then `some`, and its type. */
  private def folded(t: Term[?]): (Expr, Expr, Ty) = t.expr match
    case Expr.Match(_, List(Arm(Pattern.NoneP, n), Arm(Pattern.SomeP(_), s)), ty) => (n, s, ty)
    case other                                                                 => fail(s"not an option's fold: $other")

  test("an option's map, filter, filterNot, contains, isEmpty and toList are its folds, as an author writes them") {
    assertEquals(folded(o.map(x => x + one)), folded(o.fold(none[BigInt])(x => some(x + one))))
    assertEquals(folded(o.filter(x => one < x)),
      folded(o.fold(none[BigInt])(x => when(one < x)(some(x)).otherwise(none[BigInt]))))
    assertEquals(folded(o.filterNot(x => one < x)),
      folded(o.fold(none[BigInt])(x => when(one < x)(none[BigInt]).otherwise(some(x)))))
    assertEquals(folded(o.contains(one)), folded(o.fold(False)(a => a === one)))
    assertEquals(folded(o.isEmpty), folded(o.fold(True)(_ => False)))
    assertEquals(folded(o.toList)._3, Ty.ListOf(big))
    assertEquals(folded(o.map(x => x === one))._3, Ty.OptionOf(Ty.Bool))
  }

  test("a failing run's ifSucceeds and ifFails are the folds of its result, true on the other side") {
    val store = frflow.dsl.vocab.Declaration[BigInt => frflow.dsl.vocab.Flow[Unit]]("a number stored")
      .failsWith[BigInt]
    def closed(t: Term[Boolean]): Option[Expr] =
      frflow.dsl.node.Node.claim("Holds.")(t).alone.run.toOption.flatMap(_._2.said).map(_.value)
    assertEquals(closed(forall((n: Term[BigInt]) => store(n).ifSucceeds(r => r === r))),
      closed(forall((n: Term[BigInt]) => store(n).result.fold(_ => True, r => r === r))))
    assertEquals(closed(forall((n: Term[BigInt]) => store(n).ifFails(e => e === n))),
      closed(forall((n: Term[BigInt]) => store(n).result.fold(e => e === n, _ => True))))
    val tidy = frflow.dsl.vocab.Declaration[frflow.dsl.vocab.Flow[Unit]]("tidying").failsWith[BigInt]
    assertEquals(closed(tidy.ifSucceeds(r => r === r)), closed(tidy.result.fold(_ => True, r => r === r)))
    assertEquals(closed(tidy.ifFails(e => one < e)), closed(tidy.result.fold(e => one < e, _ => True)))
    assert(closed(tidy.ifFails(e => one < e)).nonEmpty)
  }

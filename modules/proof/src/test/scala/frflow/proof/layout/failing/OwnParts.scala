package frflow.proof.layout.failing

import frflow.core.{Kb, Lang}
import frflow.core.Nodes.*
import frflow.core.analysis.{Resolve, Resolved, Validate}
import frflow.core.code.Code
import frflow.core.name.{DefName, SourceText, SymbolName}
import frflow.core.spec.Written
import frflow.core.term.{Bound, Final, Sym}
import frflow.core.ty.Ty
import frflow.core.vocab.{Define, DefineForm}
import frflow.proof.layout.Fixture.at

/** A claim proven of code from a part about its own Definition (ruling 1 on `impl`): `total` is proven by `sumOf`,
  * a fold; `totalTwo` (a total of two then the rest) rests on its part `totalCons` (a total of one then the rest),
  * the code put in it. Each needs an induction automation does not do, so `totalCons` stays open, while `totalTwo`
  * is proven from it: the part is what its `impl` uses. And two sibling claims about the same code, `fAbove` and
  * `fAboveToo` (`inc x < f x`, false of `f x = inc x`): neither is a fact about a callee of the other's code, so
  * neither `impl` rests on the other, and both stay open.
  */
object OwnParts:
  private val big = Lang.big
  private val ints = Ty.ListOf(big)
  private val totalTy = Ty.FnOf(List(ints), big)
  private val xs = at(0, "xs", ints)
  private val sumOf = Define(DefName("sumOf"), Written.lambda(List(xs), [T[_]] => (s: Sym[T]) =>
    s.foldLeft[BigInt, BigInt](s.free(xs), Lang(s).num(0), Bound("acc", big), Bound("x", big))(s.add),
    SourceText("sumOf")), DefineForm.Function)

  private def total[T[_]](l: Lang[T], ys: T[List[BigInt]]): T[BigInt] =
    l.call(l.sym[List[BigInt] => BigInt]("total", totalTy), ys)

  /** `∀ x xs, total(x :: xs) = x + total(xs)`. */
  private val cons: Final[Boolean] = Lang.formula([T[_]] => (l: Lang[T]) => l.forall[BigInt]("x", big)(x =>
    l.forall[List[BigInt]]("xs", ints)(ys => l.s.eq(total(l, l.s.cons(x, ys)), l.s.add(x, total(l, ys))))))

  /** `∀ x y xs, total(x :: y :: xs) = x + (y + total(xs))`. */
  private val two: Final[Boolean] = Lang.formula([T[_]] => (l: Lang[T]) => l.forall[BigInt]("x", big)(x =>
    l.forall[BigInt]("y", big)(y => l.forall[List[BigInt]]("xs", ints)(ys =>
      l.s.eq(total(l, l.s.cons(x, l.s.cons(y, ys))), l.s.add(x, l.s.add(y, total(l, ys))))))))

  private val step = Ty.FnOf(List(big), big)
  private val n = at(0, "n", big)
  private val fCode = Define(DefName("fCode"), Written.lambda(List(n), [T[_]] => (s: Sym[T]) =>
    s.app(s.param[BigInt => BigInt](SymbolName("inc"), step), s.free[BigInt](n)), SourceText("fCode")),
    DefineForm.Function)
  /** `∀ x, inc(x) < f(x)`. */
  private val above: Final[Boolean] = Lang.formula([T[_]] => (l: Lang[T]) => l.forall[BigInt]("x", big)(x =>
    l.s.lt(l.call(l.sym[BigInt => BigInt]("inc", step), x), l.call(l.sym[BigInt => BigInt]("f", step), x))))

  val kb: Kb = Kb.of(claim("totalTwo")(two), claim("totalCons")(cons), claim("fAbove")(above),
      claim("fAboveToo")(above))
    .declaring(_.copy(defines = List(sumOf, fCode)))
    .naming(definition("total", totalTy), definition("f", step), definition("inc", step))
    .coding(SymbolName("total") -> Code.Proven(DefName("sumOf")), SymbolName("f") -> Code.Proven(DefName("fCode")),
      SymbolName("inc") -> Code.Provided)
    .linking(partOf("totalCons", "totalTwo"))

  lazy val resolved: Resolved = Resolve(Validate(kb.elaborated).fold(ps => throw IllegalStateException(ps.toString),
    identity))

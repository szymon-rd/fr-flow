package frflow.proof.lean.lower

import cats.syntax.all.*
import frflow.core.expr.Prog
import frflow.core.term.Stated
import frflow.proof.lean.ast.*
import frflow.proof.lean.term.Printed
import frflow.proof.terms.Commutation

/** A parallel step's two orders as `commute_i` states them: `∀ inputs (w : World), FrFlow.runOn ((do first) :
  * StateM World R) w = FrFlow.runOn ((do second) : StateM World R) w`, a traverse's two elements apart first, and
  * through `ExceptT E` with `FrFlow.runOnE` where the program may fail.
  */
final class LowerCommute(env: LowerEnv, naming: Naming):
  import Atoms.{const, name}

  def apply(c: Commutation): LExpr =
    val (scope, (inputs, apart, w)) = bound(c).run(naming).value
    val depth = c.inputs.count(_.id.value >= 0)
    def run(p: Prog[Stated[?]]): LExpr =
      val lines = LowerProg(env, depth).block(p).runA(scope).value
      val ran = LExpr.Typed(LExpr.Paren(LExpr.Do(lines, 8)), monad(c))
      LExpr.App(c.error.fold(const("FrFlow.runOn"))(e =>
        LExpr.Named(const("FrFlow.runOnE"), Names.builtin("ε"), LowerType(e))), List(ran, LExpr.Name(w)))
    val elements = apart.toList.flatMap((a, one, two) => List(one, two).map(LBinder.Explicit(_, LowerType(a.one.ty))))
    val hyps = apart.toList.flatMap { (a, one, two) =>
      val xs = Printed.term(env, scope, depth)(a.over)
      List(LExpr.Infix(LOp.Mem, LExpr.Name(one), xs), LExpr.Infix(LOp.Mem, LExpr.Name(two), xs),
        LExpr.Infix(LOp.Ne, LExpr.Name(one), LExpr.Name(two)))
    }
    val same = LExpr.Infix(LOp.Eq, run(c.first), run(c.second))
    LExpr.Forall(inputs ++ elements :+ LBinder.Explicit(w, name("World")),
      (hyps :+ same).reduceRight(LExpr.Infix(LOp.Arrow, _, _)))

  /** The names bound: the inputs, a traverse's two elements, and the world. */
  private def bound(c: Commutation) = for
    inputs <- c.inputs.traverse(x => Naming.bind(x).map(LBinder.Explicit(_, LowerType(x.ty))))
    apart  <- c.apart.traverse(a => (Naming.bind(a.one), Naming.bind(a.two)).tupled.map((one, two) => (a, one, two)))
    w      <- Naming.helper("w", Set.empty)
  yield (inputs, apart, w)

  /** `StateM World R`, or `ExceptT E (StateM World) R`. */
  private def monad(c: Commutation): LExpr =
    val world = LExpr.App(name("StateM"), List(name("World")))
    c.error.fold(LExpr.App(name("StateM"), List(name("World"), LowerType(c.result))))(e =>
      LExpr.App(name("ExceptT"), List(LowerType(e), LExpr.Paren(world), LowerType(c.result))))

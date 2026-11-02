package frflow.proof.lean.lower

import cats.syntax.all.*
import frflow.core.expr.{Binder, Prog}
import frflow.core.term.Stated
import frflow.proof.lean.ast.*
import frflow.proof.lean.term.Printed
import frflow.proof.terms.Commutation

/** A parallel step's two orders as `commute_i` states them: `∀ inputs (w : World), FrFlow.runOn ((do first) :
  * StateM World R) w = FrFlow.runOn ((do second) : StateM World R) w`, a traverse's two elements apart first, and
  * through `ExceptT E` with `FrFlow.runOnE` where the program may fail.
  *
  * Where the world holds the world's choices (a model's faults, the scheduler's races), each branch is given its own
  * (`one`, `two`: each call's failure and each race the world's choice for that call, not fixed by where the call
  * falls in one list), set as the branch begins in either order, and the two orders give the same result and the
  * same models' states, the choices left aside (`FrFlow.sameModels`). That suffices (ARCHITECTURE 4.4): a run of
  * the branches in either order on one list of choices takes a part of it per branch; given those parts each, the
  * other order gives the same, which is the written order's run on one list again, the parts in its order; and the
  * contract is proven of every list.
  */
final class LowerCommute(env: LowerEnv, naming: Naming):
  import Atoms.{const, name}

  private type P = Prog[Stated[?]]

  def apply(c: Commutation): LExpr =
    val (scope, (inputs, apart, w, choices)) = bound(c).run(naming).value
    val depth = c.inputs.count(_.id.value >= 0)
    val ran = Ran(c, scope, depth, choices, w)
    val elements = apart.toList.flatMap((a, one, two) => List(one, two).map(LBinder.Explicit(_, LowerType(a.one.ty))))
    val hyps = apart.toList.flatMap { (a, one, two) =>
      val xs = Printed.term(env, scope, depth)(a.over)
      List(LExpr.Infix(LOp.Mem, LExpr.Name(one), xs), LExpr.Infix(LOp.Mem, LExpr.Name(two), xs),
        LExpr.Infix(LOp.Ne, LExpr.Name(one), LExpr.Name(two)))
    }
    val (first, second) = (ran(c.first, List(0, 1)), ran(c.second, List(1, 0)))
    val same = choices.fold(LExpr.Infix(LOp.Eq, first, second))(_ =>
      LExpr.App(const("FrFlow.sameModels"), List(LExpr.Paren(forget), LExpr.Paren(first), LExpr.Paren(second))))
    val lists = choices.toList.flatten.flatMap(_.map(LBinder.Explicit(_, LowerFaults.listOfBool)))
    LExpr.Forall(inputs ++ elements ++ (LBinder.Explicit(w, name("World")) :: lists),
      (hyps :+ same).reduceRight(LExpr.Infix(LOp.Arrow, _, _)))

  /** An order's run from the world `w`: where the world holds choices, each branch given its own as it begins. */
  private final case class Ran(c: Commutation, scope: Naming, depth: Int, choices: Option[List[List[LeanName]]],
      w: LeanName):
    private def lower(p: P) = LowerProg(env, depth).block(p)
    // A branch bound whole, `let one ← (do …)`: a term of its own, not merged into the steps after it.
    private def branch(p: P, x: Binder) =
      (lower(p), Naming.bind(x)).mapN((ls, n) => DoLine.Bind(n, LExpr.Paren(LExpr.Do(ls, 12))))

    def apply(p: P, order: List[Int]): LExpr =
      val lines = (p, choices) match
        case (Prog.Bind(l, a, Prog.Bind(r, b, both)), Some(cs)) =>
          (for one <- branch(l, a); two <- branch(r, b); end <- lower(both)
          yield List(choose(cs(order.head)), one, choose(cs(order(1))), two) ++ end).runA(scope).value
        case _ => lower(p).runA(scope).value
      val ran = LExpr.Typed(LExpr.Paren(LExpr.Do(lines, 8)), monad(c))
      LExpr.App(c.error.fold(const("FrFlow.runOn"))(e =>
        LExpr.Named(const("FrFlow.runOnE"), Names.builtin("ε"), LowerType(e))), List(ran, LExpr.Name(w)))

  /** The world's fields of choices: the faults, and the races. */
  private def fields: List[LeanName] =
    Option.when(env.faulty)(LowerFaults.field).toList ++ Option.when(env.racing)(LowerFaults.racesField).toList

  /** `modify (fun w => { w with faults := f, races := r })`: a branch's choices, as it begins. */
  private def choose(lists: List[LeanName]): DoLine =
    val w = Names.builtin("w")
    DoLine.Step(LExpr.App(name("modify"), List(LExpr.Paren(LExpr.Fun(List(LBinder.Bare(w)),
      LExpr.Update(LExpr.Name(w), fields.zip(lists.map(LExpr.Name(_)))))))))

  /** The world with its choices left aside: what the two orders are compared on. */
  private def forget: LExpr =
    val w = Names.builtin("w")
    LExpr.Fun(List(LBinder.Bare(w)), LExpr.Update(LExpr.Name(w), fields.map(_ -> name("[]"))))

  /** The names bound: the inputs, a traverse's two elements, the world, and each branch's choices. */
  private def bound(c: Commutation) = for
    inputs  <- c.inputs.traverse(x => Naming.bind(x).map(LBinder.Explicit(_, LowerType(x.ty))))
    apart   <- c.apart.traverse(a => (Naming.bind(a.one), Naming.bind(a.two)).tupled.map((one, two) => (a, one, two)))
    w       <- Naming.helper("w", Set.empty)
    choices <- if fields.isEmpty then cats.data.State.pure(None) else
      List("one", "two").traverse(b => fields.traverse(f => Naming.helper(s"${f.text}_$b", Set.empty))).map(Some(_))
  yield (inputs, apart, w, choices)

  /** `StateM World R`, or `ExceptT E (StateM World) R`. */
  private def monad(c: Commutation): LExpr =
    val world = LExpr.App(name("StateM"), List(name("World")))
    c.error.fold(LExpr.App(name("StateM"), List(name("World"), LowerType(c.result))))(e =>
      LExpr.App(name("ExceptT"), List(LowerType(e), LExpr.Paren(world), LowerType(c.result))))


package frflow.proof.lean.lower

import cats.syntax.all.*
import frflow.core.expr.{Binder, Prog}
import frflow.core.term.Stated
import frflow.core.ty.Ty
import frflow.proof.lean.ast.*
import frflow.proof.lean.term.Printed
import frflow.proof.terms.Commutation

/** Two steps at once in their two orders as `commute_i` states them: `∀ inputs (w : World), FrFlow.runOn ((do
  * let one ← (do s); let two ← (do t); pure (one, two)) : StateM World (S × T)) w = FrFlow.runOn (… t, then s …) w`,
  * a traverse's two elements first, each a sublist's of what it is over, in one order or the other (two elements
  * of a list, which may be equal). Where the program may fail, each step is run to its own outcome
  * (`FrFlow.caught ((do …) : ExceptT E (StateM World) S)`): its failure is its side's, the other step runs.
  *
  * Where the world holds the world's choices (a model's faults, the scheduler's races), each step is given its own
  * (`one`, `two`: each call's failure and each race the world's choice for that call, not fixed by where the call
  * falls in one list), set as the step begins in either order, and the two orders give the same results and the
  * same models' states, the choices left aside (`FrFlow.sameModels`). That suffices (ARCHITECTURE 4.4): swapped
  * two at a time, every interleaving of the steps is the reading's order, each step taking the choices it took; and
  * the reading on one list takes them too, the list each step's in turn, padded where a step read past its own.
  */
final class LowerCommute(env: LowerEnv, naming: Naming):
  import Atoms.{const, name}

  private type P = Prog[Stated[?]]

  def apply(c: Commutation): LExpr =
    val (scope, (inputs, apart, w, choices)) = bound(c).run(naming).value
    val depth = c.inputs.count(_.id.value >= 0)
    val ran = Ran(c, scope, depth, choices)
    val elements = apart.toList.flatMap((a, one, two) => List(one, two).map(LBinder.Explicit(_, LowerType(a.one.ty))))
    val hyps = apart.toList.map { (a, one, two) =>
      val xs = LExpr.Paren(Printed.term(env, scope, depth)(a.over))
      def sub(x: LeanName, y: LeanName) =
        LExpr.App(const("List.Sublist"), List(LExpr.ListLit(List(LExpr.Name(x), LExpr.Name(y))), xs))
      LExpr.Paren(LExpr.Infix(LOp.Or, sub(one, two), sub(two, one)))
    }
    val (first, second) = (ran(c.first, List(0, 1), w), ran(c.second, List(1, 0), w))
    val same = choices.fold(LExpr.Infix(LOp.Eq, first, second))(_ =>
      LExpr.App(const("FrFlow.sameModels"), List(LExpr.Paren(forget), LExpr.Paren(first), LExpr.Paren(second))))
    val lists = choices.toList.flatten.flatMap(_.map(LBinder.Explicit(_, LowerFaults.listOfBool)))
    LExpr.Forall(inputs ++ elements ++ (LBinder.Explicit(w, name("World")) :: lists),
      (hyps :+ same).reduceRight(LExpr.Infix(LOp.Arrow, _, _)))

  /** An order's run from the world `w`: each step bound whole, given its own choices as it begins. */
  private final case class Ran(c: Commutation, scope: Naming, depth: Int, choices: Option[List[List[LeanName]]]):
    private def lower(p: P) = LowerProg(env, depth).block(p)
    // A step bound whole, `let one ← (do …)`: a term of its own, run to its own outcome where the program may fail.
    private def step(p: P, x: Binder) = (lower(p), Naming.bind(x)).mapN { (ls, n) =>
      val block = LExpr.Paren(LExpr.Do(ls, 12))
      DoLine.Bind(n, c.error.fold(block)(e =>
        LExpr.App(const("FrFlow.caught"), List(LExpr.Typed(block, monad(Some(e), x.ty))))))
    }

    def apply(p: P, order: List[Int], w: LeanName): LExpr =
      val lines = p match
        case Prog.Bind(l, a, Prog.Bind(r, b, both)) =>
          (for one <- step(l, a); two <- step(r, b); end <- lower(both)
          yield (chosen(order.head) ++ (one :: chosen(order(1))) :+ two) ++ end).runA(scope).value
        case _ => lower(p).runA(scope).value
      val result = (c.result, c.error) match
        case (Ty.TupleOf(ts), Some(e)) => Ty.TupleOf(ts.map(Ty.EitherOf(e, _)))
        case (other, _)                => other
      LExpr.App(const("FrFlow.runOn"), List(LExpr.Typed(LExpr.Paren(LExpr.Do(lines, 8)), monad(None, result)),
        LExpr.Name(w)))

    private def chosen(i: Int): List[DoLine] = choices.toList.map(cs => choose(cs(i)))

  /** The world's fields of choices: the faults, and the races. */
  private def fields: List[LeanName] =
    Option.when(env.faulty)(LowerFaults.field).toList ++ Option.when(env.racing)(LowerFaults.racesField).toList

  /** `modify (fun w => { w with faults := f, races := r })`: a step's choices, as it begins. */
  private def choose(lists: List[LeanName]): DoLine =
    val w = Names.builtin("w")
    DoLine.Step(LExpr.App(name("modify"), List(LExpr.Paren(LExpr.Fun(List(LBinder.Bare(w)),
      LExpr.Update(LExpr.Name(w), fields.zip(lists.map(LExpr.Name(_)))))))))

  /** The world with its choices left aside: what the two orders are compared on. */
  private def forget: LExpr =
    val w = Names.builtin("w")
    LExpr.Fun(List(LBinder.Bare(w)), LExpr.Update(LExpr.Name(w), fields.map(_ -> name("[]"))))

  /** The names bound: the inputs, a traverse's two elements, the world, and each step's choices. */
  private def bound(c: Commutation) = for
    inputs  <- c.inputs.traverse(x => Naming.bind(x).map(LBinder.Explicit(_, LowerType(x.ty))))
    apart   <- c.apart.traverse(a => (Naming.bind(a.one), Naming.bind(a.two)).tupled.map((one, two) => (a, one, two)))
    w       <- Naming.helper("w", Set.empty)
    choices <- if fields.isEmpty then cats.data.State.pure(None) else
      List("one", "two").traverse(b => fields.traverse(f => Naming.helper(s"${f.text}_$b", Set.empty))).map(Some(_))
  yield (inputs, apart, w, choices)

  /** `StateM World R`, or `ExceptT E (StateM World) R`. */
  private def monad(error: Option[Ty], result: Ty): LExpr =
    val world = LExpr.App(name("StateM"), List(name("World")))
    error.fold(LExpr.App(name("StateM"), List(name("World"), LowerType(result))))(e =>
      LExpr.App(name("ExceptT"), List(LowerType(e), LExpr.Paren(world), LowerType(result))))

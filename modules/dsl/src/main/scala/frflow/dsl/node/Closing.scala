package frflow.dsl.node

import cats.syntax.all.*
import frflow.core.expr.{Binder, Expr, Exprs, PrimOp, Quantifier}
import frflow.core.name.VarId
import frflow.core.term.{Bound, Final, Program, Sym, World}
import frflow.core.term.interpret.{Collect, Sided, Substituted}
import frflow.core.ty.Ty
import frflow.dsl.build.Fault
import frflow.dsl.run.{RunNote, Worlds}
import frflow.dsl.term.{Forall, Notes, Term}
import frflow.dsl.vocab.Called

/** A statement closed over the world it holds in (owner §41): its leading `forall`s opened (`Forall`), and, where
  * what is below them reads the current world, that world bound right below them, `∀ x…, ∀ world, …`, and each run
  * it reads (`p.result`, `p.after`) bound right below it, a run of the program from that world
  * (`Worlds.runs`); a run read as failing, both its outcomes (`runs ∧ fails`). A statement reading no world is as
  * written. So the statement holds in every reachable world, as one quantifying over a world explicitly did.
  * Refused where its reading would not be the one written: an `always` inside it (`Fault.AlwaysInside`), one
  * program's run read both as failing and plainly (`ReadTwoWays`: the plain reading is of the runs that succeed),
  * the worlds after two runs (`AfterOfTwo`: both are from the one world, not one after the other), the world read
  * without being named beside a run (`WorldUnnamed`: it would be the world before the run), and `isConstant` where
  * no step keeps it (`ConstantInside`).
  */
object Closing:
  def of(t: Term[Boolean]): Either[Fault, Term[Boolean]] =
    val (opened, body) = open(t, Nil)
    val runs = Collect.of(body.run).collect { case r: RunNote => r }.distinctBy(r => (r.key, r.error))
    val written = Term.exprOf(t).toList
    val read = Term.exprOf(body).toList
    (written.traverse_(alwaysWhole) *> written.traverse_(constants) *> oneReading(runs) *>
      read.traverse_(afterOfOne(runs, _)) *> read.traverse_(named(runs, _))).as(
      if runs.isEmpty && !Worlds.reads(body).contains(true) then t else Term(closed(opened, body, runs)))

  /** What is below the leading `forall`s, on their variables free: a statement read open, to learn what it reads
    * (`kb.Varying`); its runs, of those variables, read as they are where it is closed.
    */
  def opened(t: Term[Boolean]): Term[Boolean] = open(t, Nil)._2

  /** The leading `forall`s' bodies on free variables (`VarId.opened`), and what is below them. */
  private def open(t: Term[Boolean], opened: List[(Binder, Forall[?])]): (List[(Binder, Forall[?])], Term[Boolean]) =
    t match
      case f: Forall[a] =>
        val x = Binder(VarId.opened(opened.size), f.hint, f.bound.ty)
        open(f.opened(Term.free[a](x)(using f.bound)), opened :+ (x -> f))
      case body         => (opened, body)

  private def closed(opened: List[(Binder, Forall[?])], body: Term[Boolean], runs: List[RunNote]): Final[Boolean] =
    [T[_]] => (s: Sym[T]) =>
      type Sides = Map[Binder, Either[T[Any], T[Any]]]
      def lead(xs: List[(Binder, Forall[?])], env: Map[Binder, T[Any]]): T[Boolean] = xs match
        case (x, f) :: rest =>
          s.noted(Notes.of(f.bound.declares), s.forall(Bound[Any](f.hint, x.ty))(v => lead(rest, env + (x -> v))))
        case Nil            =>
          s.forall(Bound[World](Worlds.binder.hint, Ty.World))(w => ran(runs, env ++ Worlds.as(any(w)), Map.empty))
      def ran(rs: List[RunNote], env: Map[Binder, T[Any]], sides: Sides): T[Boolean] = rs match
        case r :: rest => run(s, r, env)((o, a) => o match
            case Left(v)     => ran(rest, env + (r.outcome -> v) + (r.after -> a), sides)
            case Right(side) => ran(rest, env + (r.after -> a), sides + (r.outcome -> side)))
        case Nil       => body.run(Sided(s, env, sides)).t
      lead(opened, Map.empty)

  /** A run from the current world, its outcome and the world after given `post`; read as failing, both outcomes,
    * each its side of the `Either` the statement reads (`Right` of what a run that succeeds gives, `Left` of the
    * error of one that fails), so a `fold` of it is the side's branch (`Sided`).
    */
  private def run[T[_]](s: Sym[T], r: RunNote, env: Map[Binder, T[Any]])(
      post: (Either[T[Any], Either[T[Any], T[Any]]], T[Any]) => T[Boolean]): T[Boolean] =
    val p = r.program.run(Substituted(s, env)).asInstanceOf[T[Program[Any]]] // a `Term[Flow[R]]`: `Program[R]`'s
    val before = env(Worlds.binder).asInstanceOf[T[World]]
    val after = Bound[World]("after", Ty.World)
    r.error match
      case None    =>
        s.runs[Any](p, before, Bound[Any]("result", r.outcomeType), after)((o, a) => post(Left(o), any(a)))
      case Some(e) =>
        val result = r.outcomeType match
          case Ty.EitherOf(_, v) => v
          case other             => other
        s.and(s.runs[Any](p, before, Bound[Any]("result", result), after)((o, a) => post(Right(Right(o)), any(a))),
          s.fails[Any, Any](p, before, Bound[Any]("error", e), after)((o, a) => post(Right(Left(o)), any(a))))

  private def any[T[_], A](t: T[A]): T[Any] = t.asInstanceOf[T[Any]]

  /** An `always` only as the whole formula: anywhere else it is no rule, and would range over every value. */
  private def alwaysWhole(e: Expr): Either[Fault, Unit] =
    val inside = e match
      case Expr.Quant(Quantifier.Always, _, body) => body
      case other                                  => other
    Either.cond(!Exprs.all(inside).exists {
      case Expr.Quant(Quantifier.Always, _, _) => true
      case _                                   => false
    }, (), Fault.AlwaysInside)

  /** Each program's run read one way in a statement: as failing everywhere, or nowhere. */
  private def oneReading(runs: List[RunNote]): Either[Fault, Unit] =
    runs.groupBy(_.key).collectFirst { case (_, rs) if rs.size > 1 => rs.head }
      .map(r => Fault.ReadTwoWays(program(r))).toLeft(())

  /** The world after one run at most: two runs are from the one world, not one after the other (owner §45 E). */
  private def afterOfOne(runs: List[RunNote], e: Expr): Either[Fault, Unit] =
    runs.filter(r => after(r, e)).distinctBy(_.key) match
      case a :: b :: _ => Left(Fault.AfterOfTwo(program(a), program(b)))
      case _           => Right(())

  /** Beside a run, every world read named: unnamed, a value would read the world before the run, whatever the
    * statement reads of it (its result, or its world after).
    */
  private def named(runs: List[RunNote], e: Expr): Either[Fault, Unit] =
    val unnamed = Worlds.unnamed(e)
    Either.cond(unnamed.isEmpty || runs.isEmpty, (), Fault.WorldUnnamed(unnamed))

  private def after(r: RunNote, e: Expr): Boolean = Exprs.all(e).contains(Expr.Var(r.after))

  private def program(r: RunNote): String = Called.of(r.program).fold("a program")(_._1.value)

  /** `isConstant` where a step keeps it: the formula, a conjunct, what `implies` gives, a `forall`'s body, a
    * branch; not of a run (owner §45 A).
    */
  private def constants(e: Expr): Either[Fault, Unit] =
    def inside(x: Expr, where: String) = Either.cond(!Exprs.all(x).exists(constant), (), Fault.ConstantInside(where))
    e match
      case Expr.Constant(_, _, v)                   =>
        Either.cond(!Exprs.all(v).exists { case Expr.Var(x) => VarId.isRan(x.id); case _ => false }, (),
          Fault.ConstantInside("of a run"))
      case Expr.Prim(PrimOp.And, as, _)             => as.traverse_(constants)
      case Expr.Prim(PrimOp.Implies, List(a, b), _) => inside(a, "left of implies") *> constants(b)
      case Expr.Prim(PrimOp.Not, _, _)              => inside(e, "under !")
      case Expr.Prim(PrimOp.Or, _, _)               => inside(e, "under ||")
      case Expr.Quant(Quantifier.Forall, _, b)      => constants(b)
      case Expr.If(c, a, b)                         => inside(c, "in a condition") *> constants(a) *> constants(b)
      case other                                    => inside(other, "inside a value")

  private def constant(e: Expr): Boolean = e match
    case Expr.Constant(_, _, _) => true
    case _                      => false

package frflow.dsl.node

import cats.syntax.all.*
import frflow.core.expr.Binder
import frflow.core.name.VarId
import frflow.core.term.{Bound, Final, Program, Sym, World}
import frflow.core.term.interpret.{Collect, Substituted}
import frflow.core.ty.Ty
import frflow.dsl.build.Fault
import frflow.dsl.run.{RunNote, Worlds}
import frflow.dsl.term.{Forall, Notes, Term}
import frflow.dsl.vocab.Called

/** A statement closed over the world it holds in (owner §41): its leading `forall`s opened (`Forall`), and, where
  * what is below them reads the current world, that world bound right below them, `∀ x…, ∀ world, …`, and each run
  * it reads (`p.result`, `p.after`) bound right below it, a run of the program from that world
  * (`Worlds.runs`); a run read as failing, both its outcomes (`runs ∧ fails`). A statement reading no world is as
  * written. So the statement holds in every reachable world, as one quantifying over a world explicitly did. One
  * program's run read both as failing and plainly is refused (`Fault.ReadTwoWays`): the plain reading is of the runs
  * that succeed, so on the failing side it would say nothing.
  */
object Closing:
  def of(t: Term[Boolean]): Either[Fault, Term[Boolean]] =
    val (opened, body) = open(t, Nil)
    val runs = Collect.of(body.run).collect { case r: RunNote => r }.distinctBy(r => (r.key, r.error))
    oneReading(runs).as(
      if runs.isEmpty && !Worlds.reads(body).contains(true) then t else Term(closed(opened, body, runs)))

  /** The leading `forall`s' bodies on free variables (`VarId.opened`), and what is below them. */
  private def open(t: Term[Boolean], opened: List[(Binder, Forall[?])]): (List[(Binder, Forall[?])], Term[Boolean]) =
    t match
      case f: Forall[a] =>
        val x = Binder(VarId.opened(opened.size), f.hint, f.bound.ty)
        open(f.opened(Term.free[a](x)(using f.bound)), opened :+ (x -> f))
      case body         => (opened, body)

  private def closed(opened: List[(Binder, Forall[?])], body: Term[Boolean], runs: List[RunNote]): Final[Boolean] =
    [T[_]] => (s: Sym[T]) =>
      def lead(xs: List[(Binder, Forall[?])], env: Map[Binder, T[Any]]): T[Boolean] = xs match
        case (x, f) :: rest =>
          s.noted(Notes.of(f.bound.declares), s.forall(Bound[Any](f.hint, x.ty))(v => lead(rest, env + (x -> v))))
        case Nil            =>
          s.forall(Bound[World](Worlds.binder.hint, Ty.World))(w => ran(runs, env + (Worlds.binder -> any(w))))
      def ran(rs: List[RunNote], env: Map[Binder, T[Any]]): T[Boolean] = rs match
        case r :: rest => run(s, r, env)((o, a) => ran(rest, env + (r.outcome -> o) + (r.after -> a)))
        case Nil       => body.run(Substituted(s, env))
      lead(opened, Map.empty)

  /** A run from the current world, its outcome and the world after given `post`; read as failing, both outcomes,
    * each its side of the `Either` the statement reads.
    */
  private def run[T[_]](s: Sym[T], r: RunNote, env: Map[Binder, T[Any]])(post: (T[Any], T[Any]) => T[Boolean])
      : T[Boolean] =
    val p = r.program.run(Substituted(s, env)).asInstanceOf[T[Program[Any]]] // a `Term[Flow[R]]`: `Program[R]`'s
    val before = env(Worlds.binder).asInstanceOf[T[World]]
    val after = Bound[World]("after", Ty.World)
    r.error match
      case None    =>
        s.runs[Any](p, before, Bound[Any]("result", r.outcomeType), after)((o, a) => post(o, any(a)))
      case Some(e) =>
        val result = r.outcomeType match
          case Ty.EitherOf(_, v) => v
          case other             => other
        s.and(s.runs[Any](p, before, Bound[Any]("result", result), after)((o, a) =>
            post(any(s.right[Any, Any](o, r.outcomeType)), any(a))),
          s.fails[Any, Any](p, before, Bound[Any]("error", e), after)((o, a) =>
            post(any(s.left[Any, Any](o, r.outcomeType)), any(a))))

  private def any[T[_], A](t: T[A]): T[Any] = t.asInstanceOf[T[Any]]

  /** Each program's run read one way in a statement: as failing everywhere, or nowhere. */
  private def oneReading(runs: List[RunNote]): Either[Fault, Unit] =
    runs.groupBy(_.key).collectFirst { case (_, rs) if rs.size > 1 => rs.head }
      .map(r => Fault.ReadTwoWays(Called.of(r.program).fold("a program")(_._1.value))).toLeft(())

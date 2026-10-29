package frflow.dsl.node

import frflow.core.expr.Binder
import frflow.core.name.VarId
import frflow.core.term.{Bound, Final, Program, Sym, World}
import frflow.core.term.interpret.{Collect, Substituted}
import frflow.core.ty.Ty
import frflow.dsl.build.{Failure, Fault}
import frflow.dsl.run.RunNote
import frflow.dsl.term.{Forall, Notes, Term}
import frflow.dsl.run.Worlds

/** A statement closed over the world it holds in (owner §41): its leading `forall`s opened (`Forall`), and, where
  * what is below them reads the current world, that world bound right below them, `∀ x…, ∀ world, …`, and each run
  * it reads (`p.result`, `p.after`) bound right below it, a run of the program from that world
  * (`Worlds.runs`); a run read as failing, both its outcomes (`runs ∧ fails`). A statement reading no world is as
  * written. So the statement holds in every reachable world, as one quantifying over a world explicitly did.
  */
object Closing:
  def of(t: Term[Boolean]): Term[Boolean] =
    val (opened, body) = open(t, Nil)
    val runs = Collect.of(body.run).collect { case r: RunNote => r }.distinctBy(r => (r.key, r.error))
    checkKeys(runs)
    if runs.isEmpty && !Worlds.reads(body.run) then t else Term(closed(opened, body, runs))

  /** The leading `forall`s' bodies on free variables (`VarId.opened`), and what is below them. */
  private def open(t: Term[Boolean], opened: List[(Binder, Forall[?])]): (List[(Binder, Forall[?])], Term[Boolean]) =
    t match
      case f: Forall[a] =>
        val x = Binder(VarId.opened(opened.size), f.hint, f.bound.ty)
        open(f.opened(Term.free[a](x)(using f.bound)), opened :+ (x -> f))
      case body         => (opened, body)

  private def closed(opened: List[(Binder, Forall[?])], body: Term[Boolean], runs: List[RunNote]): Final[Boolean] =
    [T[_]] => (s: Sym[T]) =>
      def lead(xs: List[(Binder, Forall[?])], env: Map[VarId, T[Any]]): T[Boolean] = xs match
        case (x, f) :: rest =>
          s.noted(Notes.of(f.bound.declares), s.forall(Bound[Any](f.hint, x.ty))(v => lead(rest, env + (x.id -> v))))
        case Nil            =>
          s.forall(Bound[World](Worlds.binder.hint, Ty.World))(w => ran(runs, env + (VarId.world -> any(w))))
      def ran(rs: List[RunNote], env: Map[VarId, T[Any]]): T[Boolean] = rs match
        case r :: rest => run(s, r, env)((o, a) => ran(rest, env + (r.outcome.id -> o) + (r.after.id -> a)))
        case Nil       => body.run(Substituted(s, env))
      lead(opened, Map.empty)

  /** A run from the current world, its outcome and the world after given `post`; read as failing, both outcomes,
    * each its side of the `Either` the statement reads.
    */
  private def run[T[_]](s: Sym[T], r: RunNote, env: Map[VarId, T[Any]])(post: (T[Any], T[Any]) => T[Boolean])
      : T[Boolean] =
    val p = r.program.run(Substituted(s, env)).asInstanceOf[T[Program[Any]]] // a `Term[Flow[R]]`: `Program[R]`'s
    val before = env(VarId.world).asInstanceOf[T[World]]
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

  /** Two runs whose outcomes' variables would be one: never met, but refused rather than read as one run. */
  private def checkKeys(runs: List[RunNote]): Unit =
    if runs.map(_.outcome.id).distinct.size != runs.size then
      throw Failure(Fault.Thrown("two runs of a statement are read as one: write them in two statements"))

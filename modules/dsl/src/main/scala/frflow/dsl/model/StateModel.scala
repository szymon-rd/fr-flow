package frflow.dsl.model

import cats.syntax.all.*
import frflow.core.expr.OutsideFact
import frflow.core.name.{DefName, ModelName, RelPath}
import frflow.core.term.language.Sym
import frflow.core.term.World
import frflow.core.vocab.{Fails, StateModel as Read, Symbol, SymbolType, Timed, ValueKind}
import frflow.dsl.build.{Declarations, Deferred, Fault, Site, Source}
import frflow.dsl.run.{Recorded, Worlds}
import frflow.dsl.shape.{Defines, Elab}
import frflow.dsl.term.{LeanType, Notes, Reify, Term}
import frflow.dsl.vocab.Definition
import frflow.dsl.vocab.Flow
import scala.annotation.publicInBinary
import scala.collection.mutable

/** A model of a state (owner §36), written as an object named as the model:
  * `object storedBookings extends StateModel[List[Booking]]("every booking stored, oldest first")`. Its body gives
  * each operation on the state, a Definition, its meaning over `state` (`inRoom.means(room => state.get.map(…))`);
  * the state is a field of the World, read in a statement as `storedBookings.current`, in the world it holds in.
  * The operations' plain Scala is
  * given in the FrModel (`implementTested(ops*)(start, observe)(calls)`) and tested against the model, and bound
  * where the code runs (`storedBookings := table`). What the world outside does with the state is said of it:
  * `onlyCodeChanges`, `initially(…)`, `atomic`. The meanings are kept in the order given, read once when the model is
  * first declared (`model`): an object's body gives them one statement at a time, so they are the one buffer of the
  * DSL, filled while the object is made and only read after.
  */
abstract class StateModel[S](description: String)(using named: StateModel.Named, val stateType: LeanType[S]):
  val name: ModelName = ModelName(named.name)
  /** The state, as each meaning reads and writes it. */
  protected val state: Model[S] = Model(name)(using stateType)
  private val meanings = mutable.ListBuffer.empty[Meaning]
  private val unmeant = mutable.ListBuffer.empty[Definition[?]]
  /** What a call of any of its operations fails with, if one may (`StateModel.failing`). */
  protected def fails: Option[Fails] = None
  /** What makes it the clock (FrFlow's own, `Clock.clockModel`, owner §47). */
  protected def timed: Option[Timed] = None

  extension [R](op: Definition[Flow[R]])
    inline def means(inline body: Flow[R]): Unit = meant(op, Nil, Nil)(_ => body.steps)
  extension [A, R](op: Definition[A => Flow[R]])
    inline def means(inline body: Term[A] => Flow[R])(using a: LeanType[A]): Unit =
      meant(op, List(a), Source.of(body).params)(xs => body(Term.free(xs(0))(using a)).steps)
  extension [A, B, R](op: Definition[(A, B) => Flow[R]])
    inline def means(inline body: (Term[A], Term[B]) => Flow[R])(using a: LeanType[A], b: LeanType[B]): Unit =
      meant(op, List(a, b), Source.of(body).params)(xs =>
        body(Term.free(xs(0))(using a), Term.free(xs(1))(using b)).steps)
  extension [A, B, C, R](op: Definition[(A, B, C) => Flow[R]])
    inline def means(inline body: (Term[A], Term[B], Term[C]) => Flow[R])(
        using a: LeanType[A], b: LeanType[B], c: LeanType[C]): Unit =
      meant(op, List(a, b, c), Source.of(body).params)(xs =>
        body(Term.free(xs(0))(using a), Term.free(xs(1))(using b), Term.free(xs(2))(using c)).steps)
  extension [A, B, C, D, R](op: Definition[(A, B, C, D) => Flow[R]])
    inline def means(inline body: (Term[A], Term[B], Term[C], Term[D]) => Flow[R])(
        using a: LeanType[A], b: LeanType[B], c: LeanType[C], d: LeanType[D]): Unit =
      meant(op, List(a, b, c, d), Source.of(body).params)(xs => body(Term.free(xs(0))(using a),
        Term.free(xs(1))(using b), Term.free(xs(2))(using c), Term.free(xs(3))(using d)).steps)
  extension [A, B, C, D, E, R](op: Definition[(A, B, C, D, E) => Flow[R]])
    inline def means(inline body: (Term[A], Term[B], Term[C], Term[D], Term[E]) => Flow[R])(using a: LeanType[A],
        b: LeanType[B], c: LeanType[C], d: LeanType[D], e: LeanType[E]): Unit =
      meant(op, List(a, b, c, d, e), Source.of(body).params)(xs => body(Term.free(xs(0))(using a),
        Term.free(xs(1))(using b), Term.free(xs(2))(using c), Term.free(xs(3))(using d),
        Term.free(xs(4))(using e)).steps)
  extension [A, B, C, D, E, G, R](op: Definition[(A, B, C, D, E, G) => Flow[R]])
    inline def means(inline body: (Term[A], Term[B], Term[C], Term[D], Term[E], Term[G]) => Flow[R])(
        using a: LeanType[A], b: LeanType[B], c: LeanType[C], d: LeanType[D], e: LeanType[E], h: LeanType[G]): Unit =
      meant(op, List(a, b, c, d, e, h), Source.of(body).params)(xs => body(Term.free(xs(0))(using a),
        Term.free(xs(1))(using b), Term.free(xs(2))(using c), Term.free(xs(3))(using d), Term.free(xs(4))(using e),
        Term.free(xs(5))(using h)).steps)

  extension (op: Definition[?])
    /** The operation known only by the assumptions about it (G2, owner §36: "the assumed case"), given no steps: on
      * this model's state it may give any result and leave any state but what those assumptions say
      * (`forall((q: Term[Search]) => fetch(q).result === …)`). It is a function of this model's state and its inputs:
      * two calls from one state give one result and leave one state, so a program may rely on two lookups agreeing,
      * and what it reads of the world is this model's state only (an assumption about it reads no other model,
      * `ReadsBeside`; what it needs of another is handed to it as an input). Its results are values from outside
      * (owner §37): a claim of `always` on their type is refused (`AssumedMakes`), an assumption covers them. Its Scala
      * is given with the others' and tested against those assumptions where a run can be evaluated, and against
      * itself: each call made again from the state before it must give and leave the same (`Difference.Twice`); an
      * assumption no run can evaluate is trusted, not tested, and said so.
      */
    def assumed: Unit = unmeant += op

  /** An operation's meaning, its steps recorded on its parameters' variables when the model is read. */
  @publicInBinary private[model] def meant(op: Definition[?], inputs: List[LeanType[?]], params: List[String])(
      body: Vector[frflow.core.expr.Binder] => Recorded[?]): Unit =
    meanings += Meaning(op, inputs, params, body)

  /** What `world` holds of the state (a run's world after: `storedBookings.in(book(request).after)`). */
  def in(world: Term[World]): Term[S] = Term.noted(Notes.of(declares))([T[_]] => (s: Sym[T]) =>
    s.part[S](world.run(s), name, stateType.ty))(using stateType)
  /** The state in the world a statement holds in (owner §41), or a define reading it (§43). */
  def current: Term[S] = in(Worlds.now)

  /** Nothing outside the code changes the state (owner §31, §36): which programs change it is derived. */
  def onlyCodeChanges: Fact = fact(declares, OutsideFact.OnlyCodeChanges(name))
  /** Runs on the state never interleave: one process running each atomically, or a store serializing them; each run
    * is one step of the world (owner §17, §32). So is each call of its operations against calls at once: its Scala
    * keeps two calls at once apart (one update of the state, or a store serializing them), which the model tests
    * check, running two calls at once against the model's orders of them.
    */
  def atomic: Fact = fact(declares, OutsideFact.Atomic(name))
  /** What the state starts in meets (`stored.initially(held => held === Nil)`): the rule a define named as the
    * assumption's val.
    */
  inline def initially(inline rule: Term[S] => Term[Boolean]): Fact =
    started(Defines.define(rule)(using stateType, LeanType[Boolean]))
  def started(rule: Definition[S => Boolean]): Fact =
    val f = fact(declares |+| rule.notes.declares, OutsideFact.Initially(name, DefName(rule.name.value)))
    if rule.readsWorld then Fact(Term.noted(Notes.fault(Fault.WorldRead(s"$name's initially")))(f.term.run)) else f

  /** The operations' plain Scala, made by the FrModel's `start`, as the code runs with it (`running[F](…)`). */
  def :=(instance: Any): Implemented = Implemented(name, instance)

  /** The model as the vocabulary holds it: each operation's steps over the state, read once. */
  lazy val model: Deferred[Read] = Elab.recorded(Site.Model(name)) { () =>
    val read = meanings.toList.map(_.read)
    val known = unmeant.toList.map(Meaning.assumed)
    (read.foldMap(_._1) |+| known.foldMap(_._1), Read(name, description, stateType.ty, read.map(_._2), fails,
      known.flatMap(_._2), timed))
  }

  /** What mentioning the model declares: the model, its state's type, its operations and their types. */
  def declares: Declarations = itself |+| operations.foldMap(_.leanType.declares)

  /** The model, its state's type and its operations, their types aside (what a type of the operations' may declare
    * in turn, as the clock's do).
    */
  @publicInBinary private[model] def itself: Declarations = Declarations.model(name, model) |+| stateType.declares |+|
    Declarations.in(named.at, named.name) |+|
    operations.foldMap(op => Declarations.symbol(Symbol(op.name, op.described, SymbolType.Typed(op.leanType.ty),
      ValueKind.Definition)))

  private def operations: List[Definition[?]] = meanings.toList.map(_.op) ++ unmeant.toList

  private def fact(d: Declarations, f: OutsideFact): Fact =
    Fact(Term.noted(Notes.of(d))([T[_]] => (s: Sym[T]) => s.outside(f)))

object StateModel:
  /** The name of the object a model is written as, and its file (none: FrFlow's own), read where it is written
    * (`Source.ownerName`, `Source.here`).
    */
  final case class Named(name: String, at: Option[RelPath])
  object Named:
    inline given here: Named = Named(Source.ownerName, Some(Source.here))

  /** A model any call of whose operations may fail with `error` (a store that may be down,
    * `Failure.StoreUnavailable`), changing nothing: `object stored extends StateModel.failing[S, E]("…", error)`.
    */
  abstract class failing[S, E](description: String, error: E)(using Named, LeanType[S], LeanType[E])
      extends StateModel[S](description):
    override protected def fails: Option[Fails] = Some(StateModel.fails(LeanType[E], error))
    override def declares: Declarations = super.declares |+| LeanType[E].declares

  /** The error as a value of its type: a value of a type with a `LeanType` always reads as one. */
  def fails[E](e: LeanType[E], error: E): Fails = Reify(e, error).fold(
    f => throw IllegalStateException(s"FrFlow bug: a model's error read as no value: $f"), Fails(e.ty, _))

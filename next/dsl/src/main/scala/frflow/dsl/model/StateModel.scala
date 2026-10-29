package frflow.dsl.model

import cats.syntax.all.*
import frflow.core.expr.OutsideFact
import frflow.core.name.{DefName, ModelName}
import frflow.core.term.{Program, Sym, World}
import frflow.core.vocab.{Fails, StateModel as Read, Symbol, SymbolType, ValueKind}
import frflow.dsl.build.{Declarations, Deferred, Site, Source}
import frflow.dsl.flow.Recorded
import frflow.dsl.shape.{Defines, Elab}
import frflow.dsl.term.{LeanType, Notes, Reify, Term}
import frflow.dsl.vocab.Definition
import scala.annotation.publicInBinary
import scala.collection.mutable

/** A model of a state (owner §36), written as an object named as the model:
  * `object storedBookings extends StateModel[List[Booking]]("every booking stored, oldest first")`. Its body gives
  * each operation on the state, a Definition, its meaning over `state` (`inRoom.means(room => state.get.map(…))`);
  * the state is a field of the World, read in a claim as `storedBookings.in(now)`. The operations' plain Scala is
  * given in the FrModel (`implementTested(ops*)(start, observe)(calls)`) and tested against the model, and bound
  * where the code runs (`storedBookings := table`). What the world outside does with the state is said of it:
  * `onlyCodeChanges`, `initially(…)`, `atomic`. The meanings are kept in the order given, read once when the model is
  * first declared (`model`): an object's body gives them one statement at a time, so they are the one buffer of the
  * DSL, filled while the object is made and only read after.
  */
abstract class StateModel[S](description: String)(using named: StateModel.Named, val stateType: LeanType[S]):
  val name: ModelName = ModelName(named.name)
  /** The state, as each meaning reads and writes it. */
  protected val state: Model[Recorded, S] = Model.recorded(name)(using stateType)
  private val meanings = mutable.ListBuffer.empty[Meaning]
  /** What a call of any of its operations fails with, if one may (`StateModel.failing`). */
  protected def fails: Option[Fails] = None

  extension [R](op: Definition[Program[R]])
    inline def means[X](inline body: Recorded[X])(using StateModel.Gives[R, X]): Unit = meant(op, Nil, Nil)(_ => body)
  extension [A, R](op: Definition[A => Program[R]])
    inline def means[X](inline body: Term[A] => Recorded[X])(using a: LeanType[A], g: StateModel.Gives[R, X]): Unit =
      meant(op, List(a), Source.of(body).params)(xs => body(Term.free(xs(0))(using a)))
  extension [A, B, R](op: Definition[(A, B) => Program[R]])
    inline def means[X](inline body: (Term[A], Term[B]) => Recorded[X])(
        using a: LeanType[A], b: LeanType[B], g: StateModel.Gives[R, X]): Unit =
      meant(op, List(a, b), Source.of(body).params)(xs => body(Term.free(xs(0))(using a), Term.free(xs(1))(using b)))
  extension [A, B, C, R](op: Definition[(A, B, C) => Program[R]])
    inline def means[X](inline body: (Term[A], Term[B], Term[C]) => Recorded[X])(
        using a: LeanType[A], b: LeanType[B], c: LeanType[C], g: StateModel.Gives[R, X]): Unit =
      meant(op, List(a, b, c), Source.of(body).params)(xs =>
        body(Term.free(xs(0))(using a), Term.free(xs(1))(using b), Term.free(xs(2))(using c)))
  extension [A, B, C, D, R](op: Definition[(A, B, C, D) => Program[R]])
    inline def means[X](inline body: (Term[A], Term[B], Term[C], Term[D]) => Recorded[X])(
        using a: LeanType[A], b: LeanType[B], c: LeanType[C], d: LeanType[D], g: StateModel.Gives[R, X]): Unit =
      meant(op, List(a, b, c, d), Source.of(body).params)(xs => body(Term.free(xs(0))(using a),
        Term.free(xs(1))(using b), Term.free(xs(2))(using c), Term.free(xs(3))(using d)))
  extension [A, B, C, D, E, R](op: Definition[(A, B, C, D, E) => Program[R]])
    inline def means[X](inline body: (Term[A], Term[B], Term[C], Term[D], Term[E]) => Recorded[X])(using a: LeanType[A],
        b: LeanType[B], c: LeanType[C], d: LeanType[D], e: LeanType[E], g: StateModel.Gives[R, X]): Unit =
      meant(op, List(a, b, c, d, e), Source.of(body).params)(xs => body(Term.free(xs(0))(using a),
        Term.free(xs(1))(using b), Term.free(xs(2))(using c), Term.free(xs(3))(using d), Term.free(xs(4))(using e)))
  extension [A, B, C, D, E, G, R](op: Definition[(A, B, C, D, E, G) => Program[R]])
    inline def means[X](inline body: (Term[A], Term[B], Term[C], Term[D], Term[E], Term[G]) => Recorded[X])(
        using a: LeanType[A], b: LeanType[B], c: LeanType[C], d: LeanType[D], e: LeanType[E], h: LeanType[G],
        g: StateModel.Gives[R, X]): Unit =
      meant(op, List(a, b, c, d, e, h), Source.of(body).params)(xs => body(Term.free(xs(0))(using a),
        Term.free(xs(1))(using b), Term.free(xs(2))(using c), Term.free(xs(3))(using d), Term.free(xs(4))(using e),
        Term.free(xs(5))(using h)))

  /** An operation's meaning, its steps recorded on its parameters' variables when the model is read. */
  @publicInBinary private[model] def meant(op: Definition[?], inputs: List[LeanType[?]], params: List[String])(
      body: Vector[frflow.core.expr.Binder] => Recorded[?]): Unit =
    meanings += Meaning(op, inputs, params, body)

  /** What `world` holds of the state. */
  def in(world: Term[World]): Term[S] = Term.noted(Notes.of(declares))([T[_]] => (s: Sym[T]) =>
    s.part[S](world.run(s), name, stateType.ty))(using stateType)

  /** Nothing outside the code changes the state (owner §31, §36): which programs change it is derived. */
  def onlyCodeChanges: Fact = fact(declares, OutsideFact.OnlyCodeChanges(name))
  /** Runs on the state never interleave: one process running each atomically, or a store serializing them; each run
    * is one step of the world (owner §17, §32).
    */
  def atomic: Fact = fact(declares, OutsideFact.Atomic(name))
  /** What the state starts in meets (`stored.initially(held => held === Nil)`): the rule a define named as the
    * assumption's val.
    */
  inline def initially(inline rule: Term[S] => Term[Boolean]): Fact =
    started(Defines.define(rule)(using stateType, LeanType[Boolean]))
  def started(rule: Definition[S => Boolean]): Fact =
    fact(declares |+| rule.notes.declares, OutsideFact.Initially(name, DefName(rule.name.value)))

  /** The operations' plain Scala, made by the FrModel's `start`, as the code runs with it (`running[F](…)`). */
  def :=(instance: Any): Implemented = Implemented(name, instance)

  /** The model as the vocabulary holds it: each operation's steps over the state, read once. */
  lazy val model: Deferred[Read] = Elab.recorded(Site.Model(name)) { () =>
    val read = meanings.toList.map(_.read)
    (read.foldMap(_._1), Read(name, description, stateType.ty, read.map(_._2), fails))
  }

  /** What mentioning the model declares: the model, its state's type, its operations and their types. */
  def declares: Declarations = itself |+| meanings.toList.foldMap(_.op.leanType.declares)

  /** The model, its state's type and its operations, their types aside (what a type of the operations' may declare
    * in turn, as the clock's do).
    */
  @publicInBinary private[model] def itself: Declarations = Declarations.model(name, model) |+| stateType.declares |+|
    meanings.toList.foldMap(m => Declarations.symbol(Symbol(m.op.name, m.op.described,
      SymbolType.Typed(m.op.leanType.ty), ValueKind.Definition)))

  private def fact(d: Declarations, f: OutsideFact): Fact =
    Fact(Term.noted(Notes.of(d))([T[_]] => (s: Sym[T]) => s.outside(f)))

object StateModel:
  /** The name of the object a model is written as, read where it is written (`Source.ownerName`). */
  final case class Named(name: String)
  object Named:
    inline given here: Named = Named(Source.ownerName)

  /** What a meaning's steps give: a term of the operation's result, or nothing when it gives nothing. */
  sealed trait Gives[R, X]
  object Gives:
    given term[R]: Gives[R, Term[R]] = new Gives[R, Term[R]] {}
    given nothing: Gives[Unit, Unit] = new Gives[Unit, Unit] {}

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

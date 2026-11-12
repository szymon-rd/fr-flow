package frflow.dsl.vocab

import frflow.core.name.SymbolName
import frflow.core.term.{Bound, World}
import frflow.core.term.language.{Final, Sym}
import frflow.core.ty.Ty
import frflow.core.vocab.ValueKind
import frflow.dsl.build.{Fault, Source, WrittenAt}
import frflow.dsl.run.Worlds
import frflow.dsl.term.{LeanType, Notes, Term}
import scala.annotation.unused

/** A word of the model (owner §15), of any type, named as its val (`val granted = Declaration[(RoomBookings,
  * Booking) => Boolean]("whether …")`): what statements speak of and code calls. A `Definition` is a Declaration
  * with a meaning: one made of it (`granted.define { … }`, listed in the FrModel beside the nodes), or one declared
  * and defined at once (`define { … }`, `program { … }`). A word the model gives no meaning is known through the
  * statements about it. If code calls it, it is a function the outside provides, the same in every world. If only
  * statements read it, it may change with the World (owner §43): where a statement reads it beside what does, it
  * is read in the world the statement holds in (Lean: a function of the world, the world its last input), and
  * `isConstant` assumes no run changes it.
  */
trait Declaration[A]:
  def name: SymbolName
  /** What the word means, as its declaration says it. */
  def described: String
  def leanType: LeanType[A]
  /** The word as FrFlow carries it: its symbol, a term. What FrFlow's own modules read; a model has no use for it. */
  def word: Definition[A]
  /** A program's word that can fail with an `E` (owner §46): its run read in a statement is a `Run`, its `result`
    * an `Either[E, R]`, its `after` the world either outcome leaves.
    */
  def failsWith[E](using LeanType[E]): Definition.Fails[A, E] = word.failsWith[E]
  /** The word as a curried function (`F` the curried type of `A`), in code: what plain Scala runs (`d.fn(env)`). */
  def curried[F: LeanType]: Term[F] = word.curried[F]
  /** The word's value as a term, where it is read: in a statement as the model has it, in code as it is given. */
  def term(using Reading): Term[A] = Declaration.applied[A](this, Nil)(using summon[Reading], leanType)
  /** That no run of any program from the world the statement holds in changes it, on any input (owner §44, §45 A):
    * `∀ x…, (d x…).isConstant`. It reads the World, so the word is one that changes with it (`kb.Varying`); no
    * code gives it a value, so this is an assumption.
    */
  def isConstant(using @unused st: Stating): Term[Boolean] = Term(Declaration.constant(word))

object Declaration:
  /** A word of a domain type; of a type with no `LeanType`, a code-only one, whose term has no type of its own. */
  inline def apply[A](means: String): Declaration[A] =
    Definition.plain[A](SymbolName(Source.valName), means, WrittenAt.in(Source.here))

  /** Where a term is expected, a word is its value (`booked === storedBookings.current`). */
  given value[A](using Reading): Conversion[Declaration[A], Term[A]] = _.term

  /** `d` applied to `args` where it is read. A word the model does not fix, in a statement: as the statement
    * reads it (`read`); any other: the function it is (`Definition.applied`). A program's word is code whatever
    * the model says of it: a statement reads its run.
    */
  private[dsl] def applied[R](d: Declaration[?], args: List[Term[?]])(using r: Reading, t: LeanType[R]): Term[R] =
    val w = d.word
    r.stating.filter(st => w.onTheSpot.isEmpty && !w.codeOnly && !program(w.leanType.ty) && !st.fixed(w.name))
      .fold(Definition.applied[R](w, args))(st => read[R](w, args)(using st, t))

  private def program(t: Ty): Boolean = t match
    case Ty.FnOf(_, Ty.FlowOf(_, _)) | Ty.FlowOf(_, _) => true
    case _                                             => false

  /** `d` applied to `args`, and to the world the statement holds in when it changes with it: one changing with it
    * is applied to all its inputs. The application is typed `R` by the extension that makes it, the one cast.
    */
  private def read[R](d: Definition[?], args: List[Term[?]])(using st: Stating, r: LeanType[R]): Term[R] =
    val worldly = st.varies(d.name)
    val unapplied = worldly && args.isEmpty && Worldly.parts(d.leanType.ty)._1.nonEmpty
    val all = if worldly then args :+ Worlds.current else args
    val term = Term[R]([T[_]] => (s: Sym[T]) =>
      all.foldLeft(symbol[Any](d, worldly)(s))((f, a) => ap(s)(f, a.run(s).asInstanceOf[T[Any]])).asInstanceOf[T[R]])
    if unapplied then Term.noted(Notes.fault(Fault.WorldRead(s"${d.name.value}, passed without its inputs,")))(
      term.run) else term

  private def symbol[F](d: Definition[?], worldly: Boolean): Final[F] =
    val ty = if worldly then Worldly(d.leanType.ty) else d.leanType.ty
    Symbols.written(d.at.declares(d.name.value), Symbols.term[F](d.name, d.described, ValueKind.Declaration,
      LeanType.of[Any](ty, d.leanType)))

  /** A function's term applied, its type forgotten: what `applied` types again. */
  private def ap[T[_]](s: Sym[T])(f: T[Any], a: T[Any]): T[Any] = s.app[Any, Any](f.asInstanceOf[T[Any => Any]], a)

  /** `∀ x…`, no run changing `d x…`, read in the world after it (`Worlds.constant`). */
  private def constant(d: Definition[?]): Final[Boolean] = [T[_]] => (s: Sym[T]) =>
    val (ins, _) = Worldly.parts(d.leanType.ty)
    def at(xs: List[T[Any]], w: T[World]): T[Any] =
      (xs :+ w.asInstanceOf[T[Any]]).foldLeft(symbol[Any](d, worldly = true)(s))(ap(s))
    def over(left: List[(Ty, Int)], xs: List[T[Any]]): T[Boolean] = left match
      case (ty, i) :: rest => s.forall(Bound[Any](s"x$i", ty))(x => over(rest, xs :+ x))
      case Nil             =>
        s.constant[Any](Worlds.now.run(s).asInstanceOf[T[World]], Bound[World]("after", Ty.World))(w => at(xs, w))
    over(ins.zipWithIndex, Nil)

  extension [A, R](d: Declaration[A => R])
    def apply(a: Term[A])(using Reading, LeanType[R]): Term[R] = applied(d, List(a))
  extension [A, B, R](d: Declaration[(A, B) => R])
    def apply(a: Term[A], b: Term[B])(using Reading, LeanType[R]): Term[R] = applied(d, List(a, b))
  extension [A, B, C, R](d: Declaration[(A, B, C) => R])
    def apply(a: Term[A], b: Term[B], c: Term[C])(using Reading, LeanType[R]): Term[R] = applied(d, List(a, b, c))
  extension [A, B, C, D, R](d: Declaration[(A, B, C, D) => R])
    def apply(a: Term[A], b: Term[B], c: Term[C], e: Term[D])(using Reading, LeanType[R]): Term[R] =
      applied(d, List(a, b, c, e))
  extension [A, B, C, D, E, R](d: Declaration[(A, B, C, D, E) => R])
    def apply(a: Term[A], b: Term[B], c: Term[C], e: Term[D], f: Term[E])(using Reading, LeanType[R]): Term[R] =
      applied(d, List(a, b, c, e, f))
  extension [A, B, C, D, E, G, R](d: Declaration[(A, B, C, D, E, G) => R])
    def apply(a: Term[A], b: Term[B], c: Term[C], e: Term[D], f: Term[E], g: Term[G])(using Reading, LeanType[R])
        : Term[R] = applied(d, List(a, b, c, e, f, g))

  /** A Declaration's type read in a world: the world its last input. */
  private object Worldly:
    def apply(t: Ty): Ty = parts(t) match
      case (ins, r) => Ty.FnOf(ins :+ Ty.World, r)
    def parts(t: Ty): (List[Ty], Ty) = t match
      case Ty.FnOf(ins, r) => (ins, r)
      case other           => (Nil, other)

package frflow.dsl.vocab

import frflow.core.name.SymbolName
import frflow.core.term.language.{Final, Sym}
import frflow.core.vocab.ValueKind
import frflow.dsl.build.{Source, WrittenAt}
import frflow.dsl.term.{LeanType, Term}

/** A word of the model (owner §15), of any type, named as its val (`val granted = Declaration[(RoomBookings,
  * Booking) => Boolean]("whether …")`): what statements speak of and code calls. A `Definition` is a Declaration
  * with a meaning: one made of it (`granted.define { … }`, listed in the FrModel beside the nodes), or one declared
  * and defined at once (`define { … }`). A word the model gives no meaning is known through the statements about
  * it; if code calls it, it is a function the outside provides.
  */
trait Declaration[A]:
  def name: SymbolName
  /** What the word means, as its declaration says it. */
  def described: String
  def leanType: LeanType[A]
  /** The word as FrFlow carries it: its symbol, a term. What FrFlow's own modules read; a model has no use for it. */
  def word: Definition[A]
  /** The word as a curried function (`F` the curried type of `A`), in code: what plain Scala runs (`d.fn(env)`). */
  def curried[F: LeanType]: Term[F] = word.curried[F]
  /** The word's value as a term, where it is read: in a statement as the model has it, in code as it is given. */
  def term(using Reading): Term[A] = Declaration.applied[A](this, Nil)(using summon[Reading], leanType)
object Declaration:
  /** A word of a domain type; of a type with no `LeanType`, a code-only one, whose term has no type of its own. */
  inline def apply[A](means: String): Declaration[A] =
    Definition.plain[A](SymbolName(Source.valName), means, WrittenAt.in(Source.here))

  /** Where a term is expected, a word is its value (`booked === storedBookings.current`). */
  given value[A](using Reading): Conversion[Declaration[A], Term[A]] = _.term

  /** `d` applied to `args` where it is read. A word the model does not fix, in a statement: as the statement
    * reads it (`read`); any other: the function it is (`Definition.applied`).
    */
  private[dsl] def applied[R](d: Declaration[?], args: List[Term[?]])(using r: Reading, t: LeanType[R]): Term[R] =
    val w = d.word
    r.stating.filter(st => w.onTheSpot.isEmpty && !w.codeOnly && !st.fixed(w.name))
      .fold(Definition.applied[R](w, args))(_ => read[R](w, args)(using t))

  /** `d` applied to `args`, as a word the statements alone say something of. The application is typed `R` by the
    * extension that makes it, the one cast.
    */
  private def read[R](d: Definition[?], args: List[Term[?]])(using r: LeanType[R]): Term[R] =
    Term[R]([T[_]] => (s: Sym[T]) =>
      args.foldLeft(symbol[Any](d)(s))((f, a) => ap(s)(f, a.run(s).asInstanceOf[T[Any]])).asInstanceOf[T[R]])

  private def symbol[F](d: Definition[?]): Final[F] =
    Symbols.written(d.at.declares(d.name.value), Symbols.term[F](d.name, d.described, ValueKind.Declaration,
      d.leanType))

  /** A function's term applied, its type forgotten: what `applied` types again. */
  private def ap[T[_]](s: Sym[T])(f: T[Any], a: T[Any]): T[Any] = s.app[Any, Any](f.asInstanceOf[T[Any => Any]], a)

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

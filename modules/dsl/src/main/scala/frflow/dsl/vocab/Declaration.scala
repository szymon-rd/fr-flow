package frflow.dsl.vocab

import frflow.core.name.{RelPath, SymbolName}
import frflow.core.term.{Bound, World}
import frflow.core.term.language.{Final, Sym}
import frflow.core.ty.Ty
import frflow.core.vocab.ValueKind
import frflow.dsl.build.{Fault, Source}
import frflow.dsl.run.Worlds
import frflow.dsl.term.{LeanType, Notes, Term}
import scala.annotation.{publicInBinary, unused}

/** An abstract value (owner §15), of any type, named as its val (`val authorized = Declaration[(UserId, Path) =>
  * Boolean]("whether …")`): known only through the statements about it, never called by code or a program, never
  * implemented. It is not a term: it is applied only where a statement is being written (`Stating`), so code that
  * names it does not compile. Consistency asks a witness for it, usually from what refines it. It may change with the
  * World (owner §43): where a statement reads it beside what does, it is read in the world the statement holds in
  * (Lean: a function of the world, the world its last input); `isConstant` assumes no run changes it. `at`: the file
  * it is written in.
  */
final class Declaration[A] @publicInBinary private (val name: SymbolName, val means: String, val at: RelPath)(
    using val leanType: LeanType[A]):
  /** The value as a term, in a statement. */
  def term(using Stating): Term[A] = Declaration.applied[A](this, Nil)
  /** That no run of any program from the world the statement holds in changes it, on any input (owner §44, §45 A):
    * `∀ x…, (d x…).isConstant`. It reads the World, so the Declaration is one that changes with it (`kb.Varying`);
    * no code gives it a value, so this is an assumption.
    */
  def isConstant(using @unused st: Stating): Term[Boolean] = Term(Declaration.constant(this))

object Declaration:
  inline def apply[A: LeanType](means: String): Declaration[A] = new Declaration[A](SymbolName(Source.valName), means,
    Source.here)

  /** Where a statement expects a term, a Declaration is its value (`booked === storedBookings.current`). */
  given value[A](using Stating): Conversion[Declaration[A], Term[A]] = _.term

  /** `d` applied to `args`, and to the world the statement holds in when it changes with it: one changing with it
    * is applied to all its inputs. The application is typed `R` by the extension that makes it, the one cast.
    */
  private def applied[R](d: Declaration[?], args: List[Term[?]])(using st: Stating, r: LeanType[R]): Term[R] =
    val worldly = st.varies(d.name)
    val unapplied = worldly && args.isEmpty && Worldly.parts(d.leanType.ty)._1.nonEmpty
    val all = if worldly then args :+ Worlds.current else args
    val term = Term[R]([T[_]] => (s: Sym[T]) =>
      all.foldLeft(symbol[Any](d, worldly)(s))((f, a) => ap(s)(f, a.run(s).asInstanceOf[T[Any]])).asInstanceOf[T[R]])
    if unapplied then Term.noted(Notes.fault(Fault.WorldRead(s"${d.name.value}, passed without its inputs,")))(
      term.run) else term

  private def symbol[F](d: Declaration[?], worldly: Boolean): Final[F] =
    val ty = if worldly then Worldly(d.leanType.ty) else d.leanType.ty
    Symbols.written(Some(d.at), Symbols.term[F](d.name, d.means, ValueKind.Declaration,
      LeanType.of[Any](ty, d.leanType)))

  /** A function's term applied, its type forgotten: what `applied` types again. */
  private def ap[T[_]](s: Sym[T])(f: T[Any], a: T[Any]): T[Any] = s.app[Any, Any](f.asInstanceOf[T[Any => Any]], a)

  /** `∀ x…`, no run changing `d x…`, read in the world after it (`Worlds.constant`). */
  private def constant(d: Declaration[?]): Final[Boolean] = [T[_]] => (s: Sym[T]) =>
    val (ins, _) = Worldly.parts(d.leanType.ty)
    def at(xs: List[T[Any]], w: T[World]): T[Any] =
      (xs :+ w.asInstanceOf[T[Any]]).foldLeft(symbol[Any](d, worldly = true)(s))(ap(s))
    def over(left: List[(Ty, Int)], xs: List[T[Any]]): T[Boolean] = left match
      case (ty, i) :: rest => s.forall(Bound[Any](s"x$i", ty))(x => over(rest, xs :+ x))
      case Nil             =>
        s.constant[Any](Worlds.now.run(s).asInstanceOf[T[World]], Bound[World]("after", Ty.World))(w => at(xs, w))
    over(ins.zipWithIndex, Nil)

  extension [A, R](d: Declaration[A => R])
    def apply(a: Term[A])(using Stating, LeanType[R]): Term[R] = applied(d, List(a))
  extension [A, B, R](d: Declaration[(A, B) => R])
    def apply(a: Term[A], b: Term[B])(using Stating, LeanType[R]): Term[R] = applied(d, List(a, b))
  extension [A, B, C, R](d: Declaration[(A, B, C) => R])
    def apply(a: Term[A], b: Term[B], c: Term[C])(using Stating, LeanType[R]): Term[R] = applied(d, List(a, b, c))
  extension [A, B, C, D, R](d: Declaration[(A, B, C, D) => R])
    def apply(a: Term[A], b: Term[B], c: Term[C], e: Term[D])(using Stating, LeanType[R]): Term[R] =
      applied(d, List(a, b, c, e))
  extension [A, B, C, D, E, R](d: Declaration[(A, B, C, D, E) => R])
    def apply(a: Term[A], b: Term[B], c: Term[C], e: Term[D], f: Term[E])(using Stating, LeanType[R]): Term[R] =
      applied(d, List(a, b, c, e, f))
  extension [A, B, C, D, E, G, R](d: Declaration[(A, B, C, D, E, G) => R])
    def apply(a: Term[A], b: Term[B], c: Term[C], e: Term[D], f: Term[E], g: Term[G])(using Stating, LeanType[R])
        : Term[R] = applied(d, List(a, b, c, e, f, g))

  /** A Declaration's type read in a world: the world its last input. */
  private object Worldly:
    def apply(t: Ty): Ty = parts(t) match
      case (ins, r) => Ty.FnOf(ins :+ Ty.World, r)
    def parts(t: Ty): (List[Ty], Ty) = t match
      case Ty.FnOf(ins, r) => (ins, r)
      case other           => (Nil, other)

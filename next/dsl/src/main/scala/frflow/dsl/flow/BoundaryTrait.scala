package frflow.dsl.flow

import frflow.dsl.term.Term as TermOf
import scala.quoted.*

/** A boundary trait's operations as `BoundaryMacros` reads them, in the order the trait declares them: each one's
  * name, its parameters' names and value types (`room: T[String]` is `room` and `String`), and its result's value type
  * (`F[T[RoomBookings]]` is `RoomBookings`; `F[Unit]` has none). Read off the trait applied to `Recorded` and `Term`.
  */
object BoundaryTrait:
  final case class Op(name: String, params: List[(String, Type[?])], result: Option[Type[?]], parameterless: Boolean)

  def ops[B[_[_], _[_]]: Type](using Quotes): List[Op] =
    import quotes.reflect.*
    val traitSym = TypeRepr.of[B].typeSymbol
    if !traitSym.flags.is(Flags.Trait) then report.errorAndAbort(s"FrFlow: ${traitSym.name} is not a trait")
    val applied = TypeRepr.of[B].appliedTo(List(TypeRepr.of[Recorded], TypeRepr.of[TermOf]))
    traitSym.declaredMethods.filter(_.flags.is(Flags.Deferred)).sortBy(_.pos.fold(0)(_.start))
      .map(m => op(m.name, applied.memberType(m)))

  private def op(using Quotes)(name: String, t: quotes.reflect.TypeRepr): Op =
    import quotes.reflect.*
    t match
      case MethodType(names, types, res) => res match
          case _: MethodType => report.errorAndAbort(s"FrFlow: operation $name: one parameter list")
          case _             =>
            Op(name, names.zip(types.map(valueOf(name, _))), result(name, res), parameterless = false)
      case _: PolyType     => report.errorAndAbort(s"FrFlow: operation $name: no type parameters")
      case ByNameType(res) => Op(name, Nil, result(name, res), parameterless = true)
      case res             => Op(name, Nil, result(name, res), parameterless = true)

  /** `T[A]` is `A`. */
  private def valueOf(using Quotes)(op: String, t: quotes.reflect.TypeRepr): Type[?] =
    import quotes.reflect.*
    t.dealias match
      case AppliedType(c, List(a)) if c =:= TypeRepr.of[TermOf] => a.asType
      case other => report.errorAndAbort(s"FrFlow: operation $op: a parameter is a T[…], not ${other.show}")

  /** `F[T[R]]` is `R`; `F[Unit]` is none. */
  private def result(using Quotes)(op: String, t: quotes.reflect.TypeRepr): Option[Type[?]] =
    import quotes.reflect.*
    def refused(not: String) =
      report.errorAndAbort(s"FrFlow: operation $op: its result is an F[T[…]] or an F[Unit], not $not")
    t.dealias match
      case AppliedType(f, List(r)) if f =:= TypeRepr.of[Recorded] => r.dealias match
          case _ if r =:= TypeRepr.of[Unit]                                => None
          case AppliedType(c, List(a)) if c =:= TypeRepr.of[TermOf]        => Some(a.asType)
          case other                                                       => refused(s"an F[${other.show}]")
      case other => refused(other.show)

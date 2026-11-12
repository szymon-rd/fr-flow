package frflow.dsl.service

import frflow.core.term.Selector
import frflow.core.term.language.Sym
import frflow.dsl.term.{LeanType, Term}
import frflow.dsl.vocab.{Called, Definition}

/** A member of a service called in a statement (`limits.authorise(p)`). As a term it is what the call gives
  * (`result`, `current`), made on the service as it stands, or as it is given (`in`). `after` is the service once
  * the call is made: of a member that does not change it, the service itself.
  */
final class Call[T, R] private (service: ServiceDefinition[T], called: String, args: List[Term[?]], value: Term[R],
    val after: Term[T]) extends Term[R](value.run)(using value.leanType):
  def result: Term[R] = this
  def current: Term[R] = this
  /** The same call made on the service as `state` has it (`limits.decided(id).in(limits.authorise(p).after)`). */
  def in(state: Term[T]): Call[T, R] = Call.made(service, called, state, args)

object Call:
  /** A member called with what a statement gives it: terms, or values a term is made of. */
  def of[T](service: ServiceDefinition[T], called: String, state: Term[T], args: List[Any]): Call[T, Any] =
    made(service, called, state, args.map {
      case t: Term[?] => t
      case other      => throw IllegalStateException(s"FrFlow bug: $called given $other, which is no term")
    })

  private def made[T, R](service: ServiceDefinition[T], called: String, state: Term[T], args: List[Term[?]])
      : Call[T, R] =
    val m = service.members.find(_.name == called).getOrElse(
      throw IllegalStateException(s"FrFlow bug: ${service.name.value} has no member $called"))
    given r: LeanType[R] = m.result.asInstanceOf[LeanType[R]]
    given t: LeanType[T] = service.leanType
    if !m.changes then new Call(service, called, args, applied[R](service.member(called), state :: args), state)
    else
      val did = applied[(R, T)](service.member(called), state :: args)
      new Call(service, called, args, Term.select(did, LeanType.Field(Selector.first[R, T](r.ty), r)),
        Term.select(did, LeanType.Field(Selector.second[R, T](t.ty), t)))

  /** A Definition applied to arguments whose number its type gives: what `Definition.apply` makes of one whose
    * type Scala knows.
    */
  def applied[R: LeanType](d: Definition[?], args: List[Term[?]]): Term[R] =
    val f = d.curried[Any](using d.leanType.asInstanceOf[LeanType[Any]])
    new Called[R](d.name, args, [U[_]] => (s: Sym[U]) => args.foldLeft(f.run(s))((g, a) =>
      s.app[Any, Any](g.asInstanceOf[U[Any => Any]], a.run(s).asInstanceOf[U[Any]])).asInstanceOf[U[R]])

package frflow.dsl.service

import frflow.core.term.language.Sym
import frflow.dsl.term.{LeanType, Lift, Term, Terms, TermSyntax}
import frflow.dsl.vocab.{Called, Definition}

/** A member of a service called in a statement (`limits.authorise(p)`). As a term it is what the call gives
  * (`result`, `current`), made on the service as it stands, or as it is given (`in`). `after` is the service once
  * the call is made: of a member that does not change it, the service itself.
  *
  * A member that changes the service takes steps: a class that holds no service makes its change in one; a class
  * made of services takes one for each call it makes of them. `steps` is each step taken: the service as the step
  * found it and as it left it. A call stopped by a crash leaves the service as one of its steps did. `among` is
  * the same call made among other calls, which may have changed the service before each of its steps but the
  * first; `others` is what they did.
  */
final class Call[T, R] private (made: Call.Made[T], ran: Call.Ran[T, R])
    extends Term[R](ran.value.run)(using ran.value.leanType):
  def result: Term[R] = this
  def current: Term[R] = this
  /** The service once the call is made. */
  def after: Term[T] = ran.after
  /** The same call made on the service as `state` has it (`limits.decided(id).in(limits.authorise(p).after)`). */
  def in(state: Term[T]): Call[T, R] = Call.over(made.copy(state = state))
  /** The same call made among other calls: `between` says how they left the service before a step, by the step's
    * number (the second step's is 2); before a step it does not name, they did nothing. A claim over every
    * `between` holds however the call's steps interleave with other calls'.
    */
  def among(between: Term[Map[BigInt, T]]): Call[T, R] = Call.over(made.copy(between = Some(between)))
  /** What holds of the call made among other calls, whatever they do: `holds` of the call under every schedule
    * (`processor.handle(p).amongOthers(run => run.steps.forall(step => …))`).
    */
  def amongOthers(holds: Call[T, R] => Term[Boolean]): Term[Boolean] =
    Terms.forall[Map[BigInt, T]]("between", between => holds(among(between)))(using made.schedule)
  /** Each step the call takes, in order: the service as the step found it, and as it left it. */
  def steps: Term[List[(T, T)]] = TermSyntax._1(traces)(using made.steps)
  /** What other calls did before each step but the first: the service as the call last left it, and as they left
    * it. Of a call not made `among` others, they did nothing: each pair is of one state.
    */
  def others: Term[List[(T, T)]] = TermSyntax._2(traces)(using made.steps)
  private def traces: Term[Call.Traces[T]] =
    ran.traces.getOrElse(Call.over[T, R](made.copy(between = Some(made.nobody))).traces)

object Call:
  /** What a call did among other calls: its steps, and what the others did before each (`steps`, `others`). */
  type Traces[T] = (List[(T, T)], List[(T, T)])

  /** A call as written: the service's Definition, the member, the state it is made on, what it is given, and,
    * made among other calls, their schedule. `T` is what the service's states are typed by (`State`).
    */
  private final case class Made[T](service: ServiceDeclaration[?], called: String, state: Term[T],
      args: List[Term[?]], between: Option[Term[Map[BigInt, T]]] = None):
    given LeanType[T] = service.leanType.asInstanceOf[LeanType[T]] // the service's type, by its name
    val steps: LeanType[List[(T, T)]] = LeanType[List[(T, T)]]
    val schedule: LeanType[Map[BigInt, T]] = LeanType[Map[BigInt, T]]
    val member: Member = service.members.find(_.name == called).getOrElse(
      throw IllegalStateException(s"FrFlow bug: ${service.name.value} has no member $called"))
    /** The schedule in which no other call does anything. */
    def nobody: Term[Map[BigInt, T]] = Lift.constant(Map.empty[BigInt, T])

  /** What a call gives: its value, the service after it, and, made among other calls, what was done. */
  private final case class Ran[T, R](value: Term[R], after: Term[T], traces: Option[Term[Traces[T]]])

  /** A member called with what a statement gives it: terms, or values a term is made of. */
  def of(service: ServiceDeclaration[?], called: String, state: Term[?], args: List[Any]): Call[Any, Any] =
    over(Made[Any](service, called, state.asInstanceOf[Term[Any]], args.map {
      case t: Term[?] => t
      case other      => throw IllegalStateException(s"FrFlow bug: $called given $other, which is no term")
    }))

  private def over[T, R](made: Made[T]): Call[T, R] =
    import made.given
    given LeanType[R] = made.member.result.asInstanceOf[LeanType[R]]
    val args = made.state :: made.args
    new Call(made, (made.member.changes, made.between) match
      case (false, _)            => Ran(applied[R](made.service.member(made.called), args), made.state, None)
      case (true, None)          =>
        val did = applied[(R, T)](made.service.member(made.called), args)
        Ran(TermSyntax._1(did), TermSyntax._2(did), None)
      case (true, Some(between)) =>
        val did = applied[((R, T), Traces[T])](made.service.among(made.called), made.state :: between :: made.args)
        Ran(TermSyntax._1(TermSyntax._1(did)), TermSyntax._2(TermSyntax._1(did)), Some(TermSyntax._2(did))))

  /** A Definition applied to arguments whose number its type gives: what `Definition.apply` makes of one whose
    * type Scala knows.
    */
  def applied[R: LeanType](d: Definition[?], args: List[Term[?]]): Term[R] =
    val f = d.curried[Any](using d.leanType.asInstanceOf[LeanType[Any]])
    new Called[R](d.name, args, [U[_]] => (s: Sym[U]) => args.foldLeft(f.run(s))((g, a) =>
      s.app[Any, Any](g.asInstanceOf[U[Any => Any]], a.run(s).asInstanceOf[U[Any]])).asInstanceOf[U[R]])

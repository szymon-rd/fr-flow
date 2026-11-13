package frflow.dsl.structure

import frflow.core.term.language.Sym
import frflow.dsl.term.{RocqType, Lift, Term, Terms, TermSyntax}
import frflow.dsl.vocab.{Called, Definition}
import scala.util.NotGiven

/** A member of a structure called in a statement (`limits.authorise(p)`). As a term it is what the call gives
  * (`result`, `current`), made on the structure as it stands, or as it is given (`in`). `after` is the structure once
  * the call is made: of a member that does not change it, the structure itself.
  *
  * A member that changes the structure takes steps: a class that holds no structure makes its change in one; a class
  * made of structures takes one for each call it makes of them. `steps` is each step taken: the structure as the step
  * found it and as it left it. A call stopped by a crash leaves the structure as one of its steps did. `among` is
  * the same call made among other calls, which may have changed the structure before each of its steps but the
  * first; `others` is what they did.
  */
final class Call[T, R] private (made: Call.Made[T], ran: Call.Ran[T, R])
    extends Term[R](ran.value.run)(using ran.value.rocqType):
  def result: Term[R] = this
  def current: Term[R] = this
  /** The structure once the call is made. */
  def after: Term[T] = ran.after
  /** The same call made on the structure as `state` has it (`limits.decided(id).in(limits.authorise(p).after)`). */
  def in(state: Term[T]): Call[T, R] = Call.over(made.copy(state = state))
  /** The same call made on the structure as the one that holds it has it: `holder` is a state of a structure
    * whose class is given this one's word (`ledger.posted(id).in(handler.handle(p).after)`).
    */
  def in[H <: String](holder: Term[State[H]])(using NotGiven[State[H] =:= T]): Call[T, R] =
    in(Call.heldIn[T](made.structure, holder))
  /** The same call made among other calls: `between` says how they left the structure before a step, by the step's
    * number (the second step's is 2); before a step it does not name, they did nothing. A claim over every
    * `between` holds however the call's steps interleave with other calls'.
    */
  def among(between: Term[Map[BigInt, T]]): Call[T, R] = Call.over(made.copy(between = Some(between)))
  /** What holds of the call made among other calls, whatever they do: `holds` of the call under every schedule
    * (`handler.handle(p).amongOthers(run => run.steps.forall(step => …))`).
    */
  def amongOthers(holds: Call[T, R] => Term[Boolean]): Term[Boolean] =
    Terms.forall[Map[BigInt, T]]("between", between => holds(among(between)))(using made.schedule)
  /** Each step the call takes, in order: the structure as the step found it, and as it left it. */
  def steps: Term[List[(T, T)]] = TermSyntax._1(traces)(using made.steps)
  /** What other calls did before each step but the first: the structure as the call last left it, and as they left
    * it. Of a call not made `among` others, they did nothing: each pair is of one state.
    */
  def others: Term[List[(T, T)]] = TermSyntax._2(traces)(using made.steps)
  private def traces: Term[Call.Traces[T]] =
    ran.traces.getOrElse(Call.over[T, R](made.copy(between = Some(made.nobody))).traces)

object Call:
  /** What a call did among other calls: its steps, and what the others did before each (`steps`, `others`). */
  type Traces[T] = (List[(T, T)], List[(T, T)])

  /** A call as written: the structure's Definition, the member, the state it is made on, what it is given, and,
    * made among other calls, their schedule. `T` is what the structure's states are typed by (`State`).
    */
  private final case class Made[T](structure: StructureDeclaration[?], called: String, state: Term[T],
      args: List[Term[?]], between: Option[Term[Map[BigInt, T]]] = None):
    given RocqType[T] = structure.rocqType.asInstanceOf[RocqType[T]] // the structure's type, by its name
    val steps: RocqType[List[(T, T)]] = RocqType[List[(T, T)]]
    val schedule: RocqType[Map[BigInt, T]] = RocqType[Map[BigInt, T]]
    val member: Member = structure.members.find(_.name == called).getOrElse(
      throw IllegalStateException(s"FrFlow bug: ${structure.name.value} has no member $called"))
    /** The schedule in which no other call does anything. */
    def nobody: Term[Map[BigInt, T]] = Lift.constant(Map.empty[BigInt, T])

  /** What a call gives: its value, the structure after it, and, made among other calls, what was done. */
  private final case class Ran[T, R](value: Term[R], after: Term[T], traces: Option[Term[Traces[T]]])

  /** A member called with what a statement gives it: terms, or values a term is made of. */
  def of(structure: StructureDeclaration[?], called: String, state: Term[?], args: List[Any]): Call[Any, Any] =
    over(Made[Any](structure, called, state.asInstanceOf[Term[Any]], args.map {
      case t: Term[?] => t
      case other      => throw IllegalStateException(s"FrFlow bug: $called given $other, which is no term")
    }))

  private def over[T, R](made: Made[T]): Call[T, R] =
    import made.given
    given RocqType[R] = made.member.result.asInstanceOf[RocqType[R]]
    val args = made.state :: made.args
    new Call(made, (made.member.changes, made.between) match
      case (false, _)            => Ran(applied[R](made.structure.member(made.called), args), made.state, None)
      case (true, None)          =>
        val did = applied[(R, T)](made.structure.member(made.called), args)
        Ran(TermSyntax._1(did), TermSyntax._2(did), None)
      case (true, Some(between)) =>
        val did = applied[((R, T), Traces[T])](made.structure.among(made.called), made.state :: between :: made.args)
        Ran(TermSyntax._1(TermSyntax._1(did)), TermSyntax._2(TermSyntax._1(did)), Some(TermSyntax._2(did))))

  /** A structure as the structure in the state `holder` holds it. */
  def heldIn[T](structure: StructureDeclaration[?], holder: Term[?]): Term[T] =
    applied[T](StructureDeclaration.held(holder.rocqType, structure.name, structure.rocqType), List(holder))(
      using structure.rocqType.asInstanceOf[RocqType[T]])

  /** A Definition applied to arguments whose number its type gives: what `Definition.apply` makes of one whose
    * type Scala knows.
    */
  def applied[R: RocqType](d: Definition[?], args: List[Term[?]]): Term[R] =
    val f = d.curried[Any](using d.rocqType.asInstanceOf[RocqType[Any]])
    new Called[R](d.name, args, [U[_]] => (s: Sym[U]) => args.foldLeft(f.run(s))((g, a) =>
      s.app[Any, Any](g.asInstanceOf[U[Any => Any]], a.run(s).asInstanceOf[U[Any]])).asInstanceOf[U[R]])

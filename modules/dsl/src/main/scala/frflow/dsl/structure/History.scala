package frflow.dsl.structure

import frflow.core.term.language.Sym
import frflow.dsl.term.{RocqType, Term, Terms}
import frflow.dsl.term.TermSyntax.{=!=, False, True}

/** Calls that change a structure, made one after another (`later: links.History`): a list of what each was. One
  * call is the member that changes the structure and what it was given (`Did`): of a structure with one such member,
  * its input; of one with more, an `Either` over them in the order the trait declares them (`Either[Url, Code]`: a
  * URL shortened, or a code removed). A member taking nothing is given `Unit`; one taking more than one input is not
  * read yet.
  */
private[structure] object History:
  private type Calls = Term[List[Any]]

  private def changing(s: StructureDeclaration[?]): List[Member] = s.members.filter(_.changes)

  private def given1(m: Member): RocqType[Any] = m.params match
    case Nil      => RocqType[Unit].asInstanceOf[RocqType[Any]]
    case p :: Nil => p.asInstanceOf[RocqType[Any]]
    case _        => throw IllegalStateException(s"FrFlow: a history of calls is not read of a structure whose " +
        s"member ${m.name} takes more than one input")

  private def did(ms: List[Member]): RocqType[Any] = ms match
    case Nil       => RocqType[Unit].asInstanceOf[RocqType[Any]]
    case m :: Nil  => given1(m)
    case m :: rest => RocqType.either(using given1(m), did(rest)).asInstanceOf[RocqType[Any]]

  /** What `each` gives of the member a call was and what it was given. */
  private def onEach[R: RocqType](ms: List[Member], call: Term[Any])(each: (Member, Term[Any]) => Term[R]): Term[R] =
    ms match
      case Nil       => throw IllegalStateException("FrFlow bug: a call of a structure nothing changes")
      case m :: Nil  => each(m, call)
      case m :: rest => Terms.foldEither[Any, Any, R](call.asInstanceOf[Term[Either[Any, Any]]], ("given", "other"))(
          input => each(m, input), other => onEach(rest, other)(each))(using given1(m), did(rest), RocqType[R])

  /** The structure once every call of `later` has been made, in order, from the state `made` is made on. */
  def after[T](made: Call.Made[T], later: Calls): Term[T] =
    import made.given
    val ms = changing(made.structure)
    if ms.isEmpty then made.state
    else Terms.foldLeft[Any, T](later, made.state, ("state", "call"))((state, call) =>
      onEach[T](ms, call)((m, input) => Call.over[T, Any](made.copy(called = m.name, state = state,
        args = if m.params.isEmpty then Nil else List(input), between = None)).after))(using did(ms))

  /** No call of `later` is the call `made`: the same member given the same. */
  def never(made: Call.Made[?], later: Calls): Term[Boolean] =
    val ms = changing(made.structure)
    if !made.member.changes then throw IllegalStateException(s"FrFlow: ${made.called} does not change " +
      s"${made.structure.name.value}: no history of its calls has it")
    Terms.over[List[Any], Any, Boolean, Boolean](later, "call", call => onEach[Boolean](ms, call)((m, input) =>
      if m.name != made.called then True
      else made.args.headOption.fold(False)(asked => input =!= asked.asInstanceOf[Term[Any]])))(
      [T[_]] => (s: Sym[T]) => s.all[Any])(using did(ms), RocqType[Boolean])

/** What a statement says of the calls made later (`later: links.History`). */
object HistorySyntax:
  extension [D](later: Term[List[D]])
    /** No call of `later` is `call`: the same member given the same is not among them
      * (`later.never(links.remove(code))`).
      */
    def never(call: Call[?, ?]): Term[Boolean] = call.notAmong(later)

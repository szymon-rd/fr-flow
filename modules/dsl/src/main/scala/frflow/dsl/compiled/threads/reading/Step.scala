package frflow.dsl.compiled.threads.reading

import frflow.core.threads.Term

/** One statement of a program, before what follows it: `name <- program ;;`, `let name := value in`, or
  * `let (names) := value in`.
  */
private[threads] enum Step:
  case Bind(name: String, program: Term)
  case Let(name: String, value: Term)
  case Unpack(names: List[String], value: Term)

  /** The names it mentions. */
  def mentions: List[String] = this match
    case Bind(_, program) => program.mentions
    case Let(_, value)    => value.mentions
    case Unpack(_, value) => value.mentions

  /** The names it binds (`_` binds none). */
  def bound: List[String] = (this match
    case Bind(name, _)    => List(name)
    case Let(name, _)     => List(name)
    case Unpack(names, _) => names).filterNot(_ == "_")

private[threads] object Step:
  /** `steps`, then `last`. */
  def before(steps: List[Step], last: Term): Term = steps.foldRight(last) {
    case (Bind(name, program), rest) => Term.Bind(name, program, rest)
    case (Let(name, value), rest)    => Term.Let(name, value, rest)
    case (Unpack(names, value), rest) => Term.Unpack(names, value, rest) }

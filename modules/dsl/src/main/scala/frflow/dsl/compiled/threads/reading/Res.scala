package frflow.dsl.compiled.threads.reading

import frflow.core.threads.{Term, Ty}

/** An expression read: once `steps` have run, `term` is its value, of type `ty`, or the program that gives it. */
private[threads] final case class Res(steps: List[Step], term: Term, ty: Ty, kind: Res.Kind):
  def isValue: Boolean = kind == Res.Kind.Value

  /** The whole as one program. */
  def program: Term = Step.before(steps, if isValue then Term.ret(term) else term)

  /** The names it mentions, its steps' and its term's. */
  def mentions: List[String] = steps.flatMap(_.mentions) ++ term.mentions

private[threads] object Res:
  enum Kind:
    case Value, Program

  def value(term: Term, ty: Ty): Res = Res(Nil, term, ty, Kind.Value)
  def program(term: Term, ty: Ty): Res = Res(Nil, term, ty, Kind.Program)

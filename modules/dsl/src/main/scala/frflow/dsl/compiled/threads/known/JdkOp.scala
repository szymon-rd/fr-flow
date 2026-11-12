package frflow.dsl.compiled.threads.known

import frflow.core.threads.Ty

/** An operation of `Jdk.v`, as a method of the JDK is read: its name, the types of its arguments and of what it
  * gives, and whether the object the method is called on is its first argument.
  */
final case class JdkOp(name: String, takes: List[Ty], gives: Ty, on: JdkOp.On)

object JdkOp:
  /** The operations that change nothing, always return and never throw: one not evaluated is not missed. */
  val silent: Set[String] = Set("CurrentThread")

  /** What becomes of the object a method is called on. */
  enum On:
    /** It is the operation's first argument. */
    case First
    /** There is none (a static method, a constructor), or the operation does not read it. */
    case Absent

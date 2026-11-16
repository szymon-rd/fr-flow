package frflow.core.code

import frflow.core.expr.Value
import frflow.core.name.{DefName, SymbolName}
import frflow.core.threads.Datum

/** What is known of the classes code mentions, read from their class files: the classes of the JDK whose objects
  * are known by their identity (they keep `Object`'s `equals`), the classes of what is thrown, the one method
  * of each interface a function can be taken as (`"java.lang.Runnable run "`), and the classes outside the JDK
  * that are below a class known by its identity (an object of the code may be of one).
  */
final case class ClassFacts(identities: List[String], throwables: List[String], functions: List[String],
    heirs: List[String]):
  def ++(more: ClassFacts): ClassFacts = ClassFacts((identities ++ more.identities).distinct.sorted,
    (throwables ++ more.throwables).distinct.sorted, (functions ++ more.functions).distinct.sorted,
    (heirs ++ more.heirs).distinct.sorted)

object ClassFacts:
  val none: ClassFacts = ClassFacts(Nil, Nil, Nil, Nil)

/** A file of code read from its TASTy: its name, the tree it holds, and what is known of the classes it
  * mentions.
  */
final case class ReadUnit(name: String, tree: Datum, classes: ClassFacts)

/** What gives a Definition its meaning (owner §15): proven code (a define), plain Scala tested by properties, a
  * value fixed in the model, a value provided where the code runs (bound by examples, drawn by tests, passed in
  * production), or an execution of code read from its TASTy as trees (`Executing`: every statement about it is
  * stated of an execution of that code, and Rocq says what that is).
  */
enum Code:
  case Proven(define: DefName)
  case Tested(runs: ScalaCode, calls: List[SymbolName])
  case Valued(value: Value)
  case Provided
  case Executing(units: List[ReadUnit])

  /** The define Rocq proves, if any. */
  def proven: Option[DefName] = this match
    case Proven(d) => Some(d)
    case _         => None

  /** The Scala code it runs, if any. */
  def scala: Option[ScalaCode] = this match
    case Tested(r, _) => Some(r)
    case _            => None

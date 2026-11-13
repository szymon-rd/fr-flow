package frflow.dsl.vocab

import frflow.core.name.SymbolName
import frflow.dsl.term.{RocqType, Term}
import scala.annotation.implicitNotFound

/** That a statement is being written: inside `Node.claim`, `Node.assumption` or an example, and in the body of a
  * `stated` define, which only a statement may call. A word read there (`Reading`) is read as the model has it. It
  * knows which words the model fixes (`fixed`: those it gives a meaning, and those its code calls). While a statement
  * is read to learn what it reads (`closing` false), it is left open. It also knows which structures the model has held
  * by which (`holds`: a structure's word, and the words of the structures whose classes are given it).
  */
@implicitNotFound("FrFlow: this is said only in a statement (Node.claim, Node.assumption, an example, a stated " +
  "define)")
final class Stating private (val closing: Boolean, val fixed: Set[SymbolName],
    states: Map[SymbolName, Term[?]] = Map.empty, told: (SymbolName, RocqType[?]) => Unit = (_, _) => (),
    val holds: Map[SymbolName, Set[SymbolName]] = Map.empty):
  /** A structure as it stands, as the statement reads it (`limits.authorise(p)`, `limits.current`): the variable the
    * statement binds it to, so a claim holds of the structure in every state (`Standing.closing`); where none is
    * bound (an example's fact), the structure's own word, a value the example gives.
    */
  def standing[T](structure: Declaration[T]): Term[T] =
    told(structure.name, structure.rocqType)
    states.get(structure.name).fold(structure.word: Term[T])(_.asInstanceOf[Term[T]])
  /** The same statement, each structure read as the variable `bound` gives it. */
  private[dsl] def holding(bound: Map[SymbolName, Term[?]]): Stating =
    Stating(closing, fixed, bound, told, holds)
  /** The same statement, `heard` told each structure it reads as it stands. */
  private[dsl] def asking(heard: (SymbolName, RocqType[?]) => Unit): Stating =
    Stating(closing, fixed, states, heard, holds)

object Stating:
  /** A statement written alone (an example's fact). */
  private[dsl] val writing: Stating = Stating(closing = true, Set.empty)
  /** While a statement is read open, to learn what it reads (the structures it reads as they stand). `fixed`: the
    * words the model gives a meaning or its code calls (`kb.Elaborate.fixed`).
    */
  private[dsl] def probing(fixed: Set[SymbolName]): Stating = Stating(closing = false, fixed)
  private[dsl] val probing: Stating = probing(Set.empty)
  /** A statement of a model: what the model fixes, and which structures it has held by which. */
  private[dsl] def reading(fixed: Set[SymbolName], holds: Map[SymbolName, Set[SymbolName]]): Stating =
    Stating(closing = true, fixed, holds = holds)

/** Where a word is read: in a statement, which knows what the model fixes, or in code (a define's body, plain
  * Scala), where a word is the function it is given as.
  */
final class Reading private[vocab] (val stating: Option[Stating])

object Reading extends ReadingInCode:
  given stated(using st: Stating): Reading = Reading(Some(st))

private[vocab] trait ReadingInCode:
  given code: Reading = Reading(None)

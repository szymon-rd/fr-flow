package frflow.dsl.vocab

import frflow.core.name.SymbolName
import frflow.dsl.term.{LeanType, Term}
import scala.annotation.implicitNotFound

/** That a statement is being written: inside `Node.claim`, `Node.assumption` or an example, and in the body of a
  * `stated` define, which only a statement may call. A word read there (`Reading`) is read as the model has it. It
  * knows which words the model fixes (`fixed`: those it gives a meaning, and those its code calls) and which of
  * the others change with the World (`varies`, owner §43): those a statement reads beside what does, the FrModel
  * reading them off its statements (`kb.Elaborate`); each of them is read in the world the statement holds in.
  * While they are read off (`closing` false), a statement is left open.
  */
@implicitNotFound("FrFlow: this is said only in a statement (Node.claim, Node.assumption, an example, a stated " +
  "define)")
final class Stating private (val varies: Set[SymbolName], val closing: Boolean, val fixed: Set[SymbolName],
    states: Map[SymbolName, Term[?]] = Map.empty, told: (SymbolName, LeanType[?]) => Unit = (_, _) => ()):
  /** A structure as it stands, as the statement reads it (`limits.authorise(p)`, `limits.current`): the variable the
    * statement binds it to, so a claim holds of the structure in every state (`Standing.closing`); where none is
    * bound (an example's fact), the structure's own word, a value the example gives.
    */
  def standing[T](structure: Declaration[T]): Term[T] =
    told(structure.name, structure.leanType)
    states.get(structure.name).fold(structure.word: Term[T])(_.asInstanceOf[Term[T]])
  /** The same statement, each structure read as the variable `bound` gives it. */
  private[dsl] def holding(bound: Map[SymbolName, Term[?]]): Stating = Stating(varies, closing, fixed, bound, told)
  /** The same statement, `heard` told each structure it reads as it stands. */
  private[dsl] def asking(heard: (SymbolName, LeanType[?]) => Unit): Stating =
    Stating(varies, closing, fixed, states, heard)

object Stating:
  /** A statement written alone (an example's fact): nothing it mentions is read as changing with the World. */
  private[dsl] val writing: Stating = Stating(Set.empty, closing = true, Set.empty)
  /** While what changes with the World is read off the statements: none of them closed. `fixed`: the words the
    * model gives a meaning or its code calls (`kb.Elaborate.fixed`).
    */
  private[dsl] def probing(fixed: Set[SymbolName]): Stating = Stating(Set.empty, closing = false, fixed)
  private[dsl] val probing: Stating = probing(Set.empty)
  private[dsl] def varying(declarations: Set[SymbolName], fixed: Set[SymbolName]): Stating =
    Stating(declarations, closing = true, fixed)

/** Where a word is read: in a statement, which knows what the model fixes and what changes with the World, or in
  * code (a define's body, a program's, plain Scala), where a word is the function it is given as.
  */
final class Reading private[vocab] (val stating: Option[Stating])

object Reading extends ReadingInCode:
  given stated(using st: Stating): Reading = Reading(Some(st))

private[vocab] trait ReadingInCode:
  given code: Reading = Reading(None)

package frflow.dsl.vocab

import frflow.core.name.SymbolName
import frflow.dsl.term.{LeanType, Term}
import scala.annotation.implicitNotFound

/** That a statement is being written: inside `Node.claim`, `Node.assumption` or an example, and in the body of a
  * `stated` define, which only a statement may call. Only there may a Declaration be applied. A `define`, a `program`
  * and plain Scala are written without it, so a Declaration used by code does not compile (owner §15). It knows
  * which Declarations change with the World (`varies`, owner §43): those a statement reads beside what does, the
  * FrModel reading them off its statements (`kb.Elaborate`); each of them is read in the world the statement holds in.
  * While they are read off (`closing` false), a statement is left open.
  */
@implicitNotFound("FrFlow: a Declaration is used only in statements (Node.claim, Node.assumption, an example, a " +
  "stated define); code, defines and programs use Definitions")
final class Stating private (val varies: Set[SymbolName], val closing: Boolean,
    states: Map[SymbolName, Term[?]] = Map.empty, told: (SymbolName, LeanType[?]) => Unit = (_, _) => ()):
  /** A service as it stands, as the statement reads it (`limits.authorise(p)`, `limits.current`): the variable the
    * statement binds it to, so a claim holds of the service in every state (`Serving.closing`); where none is
    * bound (an example's fact), the service's own Definition, a value the example gives.
    */
  def standing[T](service: Definition[T]): Term[T] =
    told(service.name, service.leanType)
    states.get(service.name).fold(service: Term[T])(_.asInstanceOf[Term[T]])
  /** The same statement, each service read as the variable `bound` gives it. */
  private[dsl] def holding(bound: Map[SymbolName, Term[?]]): Stating = Stating(varies, closing, bound, told)
  /** The same statement, `heard` told each service it reads as it stands. */
  private[dsl] def asking(heard: (SymbolName, LeanType[?]) => Unit): Stating = Stating(varies, closing, states, heard)

object Stating:
  /** A statement written alone (an example's fact): nothing it mentions is read as changing with the World. */
  private[dsl] val writing: Stating = Stating(Set.empty, closing = true)
  /** While what changes with the World is read off the statements: none of them closed. */
  private[dsl] val probing: Stating = Stating(Set.empty, closing = false)
  private[dsl] def varying(declarations: Set[SymbolName]): Stating = Stating(declarations, closing = true)

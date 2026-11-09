package frflow.dsl.vocab

import frflow.core.name.SymbolName
import scala.annotation.implicitNotFound

/** That a statement is being written: inside `Node.claim`, `Node.assumption` or an example, and in the body of a
  * `stated` define, which only a statement may call. Only there may a Declaration be applied. A `define`, a `program`
  * and plain Scala are written without it, so a Declaration used by code does not compile (owner §15). It knows which Declarations change with the World (`varies`, owner §43): those a
  * statement reads beside what does, the FrModel reading them off its statements (`kb.Elaborate`); each of them is
  * read in the world the statement holds in. While they are read off (`closing` false), a statement is left open.
  */
@implicitNotFound("FrFlow: a Declaration is used only in statements (Node.claim, Node.assumption, an example, a " +
  "stated define); code, defines and programs use Definitions")
final class Stating private (val varies: Set[SymbolName], val closing: Boolean)

object Stating:
  /** A statement written alone (an example's fact): nothing it mentions is read as changing with the World. */
  private[dsl] val writing: Stating = Stating(Set.empty, closing = true)
  /** While what changes with the World is read off the statements: none of them closed. */
  private[dsl] val probing: Stating = Stating(Set.empty, closing = false)
  private[dsl] def varying(declarations: Set[SymbolName]): Stating = Stating(declarations, closing = true)

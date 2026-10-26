package frflow.dsl.vocab

import scala.annotation.implicitNotFound

/** That a statement is being written: inside `Node.claim`, `Node.assumption` or an example. Only there may a
  * Declaration be applied. A `define`, a `program` and plain Scala are written without it, so a Declaration used by
  * code does not compile (owner §15).
  */
@implicitNotFound("FrFlow: a Declaration is used only in statements (Node.claim, Node.assumption, an example); " +
  "code, defines and programs use Definitions")
sealed trait Stating

object Stating:
  private[dsl] val writing: Stating = new Stating {}

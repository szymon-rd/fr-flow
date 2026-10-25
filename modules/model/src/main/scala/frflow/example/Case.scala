package frflow
package example

/** A case of a contract on an operation of type `F`: a call's inputs and result; a flow's run, its inputs and the world
  * before, and its result with the world after.
  */
final case class Case[F] private[frflow] (inputs: List[Any], result: Any, expected: Boolean, note: String)

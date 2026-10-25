package frflow
package node

/** What a contract on a flow says of a run that fails with an error of type `err`: `post(error, before, after)`, or,
  * with none, that it changes nothing (every model's state after it is as before).
  */
final case class FailureClause(err: LeanType[?], post: Option[Lifted[?]]):
  def changesNothing: Boolean = post.isEmpty
  def describe: String = post.fold(s"a run that fails (${Types.scala(err)}) changes nothing")(p => s"a run that fails (${Types.scala(err)}): ${p.source}")

package frflow.testing.derive

import frflow.core.expr.Value
import frflow.core.ty.Ty

/** The values one case has drawn of each type that recurs (strings, numbers, records), a few of each: what its next
  * value of the type may be, so the token asked about is often one the session table holds.
  */
final case class Pool(drawn: Map[Ty, Vector[Value]]):
  def of(ty: Ty): Vector[Value] = drawn.getOrElse(ty, Vector.empty)

  /** `v` kept for the case's next values of `ty`, while it keeps fewer than `Pool.Kept`. */
  def kept(ty: Ty, v: Value): Pool =
    if !Pool.recurs(ty) || of(ty).size >= Pool.Kept || of(ty).contains(v) then this
    else Pool(drawn.updated(ty, of(ty) :+ v))

object Pool:
  val empty: Pool = Pool(Map.empty)
  val Kept: Int = 4

  /** How often a case's next value of a type is one it drew before: a string often (a token asked about, one a table
    * holds); a number or a record less (a list of records, all one, seldom meets a rule over pairs of them).
    */
  def reuse(ty: Ty): Double = ty match
    case Ty.Str => 0.6
    case _      => 0.25

  def recurs(ty: Ty): Boolean = ty match
    case Ty.Str | Ty.Num(_) | Ty.Data(_) => true
    case _                               => false

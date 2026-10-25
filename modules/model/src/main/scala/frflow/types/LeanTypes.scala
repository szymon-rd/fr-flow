package frflow
package types

/** `of[T]`, a Scala type's Lean type where a definition names one (re-exported by `frflow`). */
object LeanTypes:
  /** The Lean translation of a Scala type: `User := of[UserId]`. */
  def of[T](using t: LeanType[T]): LeanType[T] = t

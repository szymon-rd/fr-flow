package frflow
package types

/** The fields of a case class (or of an enum's case): their names and types, found as any given is. */
trait FieldsOf[Ts <: Tuple, Ls <: Tuple]:
  private[frflow] def list: List[(String, LeanType[?])]

object FieldsOf:
  given FieldsOf[EmptyTuple, EmptyTuple] with
    private[frflow] def list = Nil
  given [H, T <: Tuple, L <: String, Ls <: Tuple](using h: LeanType[H], l: ValueOf[L], t: FieldsOf[T, Ls]): FieldsOf[H *: T, L *: Ls] with
    private[frflow] def list = (l.value -> h) :: t.list

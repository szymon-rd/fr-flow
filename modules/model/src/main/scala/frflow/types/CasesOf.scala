package frflow
package types

import scala.deriving.Mirror

/** The cases of an enum, in order. */
trait CasesOf[Cs <: Tuple, Ls <: Tuple]:
  private[frflow] def list(owner: String): List[Ctor]

object CasesOf:
  given CasesOf[EmptyTuple, EmptyTuple] with
    private[frflow] def list(owner: String) = Nil
  given [C, Cs <: Tuple, L <: String, Ls <: Tuple](using m: Mirror.ProductOf[C], f: FieldsOf[m.MirroredElemTypes, m.MirroredElemLabels],
      l: ValueOf[L], rest: CasesOf[Cs, Ls]): CasesOf[C *: Cs, L *: Ls] with
    private[frflow] def list(owner: String) =
      val fs = f.list
      // A case without fields is a value of the enum (`Search.Everything`).
      Ctor(l.value, s"$owner.${Names.ident(l.value)}", fs, Option.when(fs.isEmpty)(m.fromProduct(EmptyTuple)), LeanType.maker(m)) ::
        rest.list(owner)

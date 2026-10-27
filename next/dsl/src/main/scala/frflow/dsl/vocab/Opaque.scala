package frflow.dsl.vocab

import frflow.core.name.TypeName
import frflow.core.ty.Ty
import frflow.core.vocab.Sort
import frflow.dsl.build.{Declarations, Source}
import frflow.dsl.term.LeanType

/** A domain type, open until a definition fixes it, named as its val: `val User = Opaque(means)`, used as `User.T`. */
final class Opaque(val name: TypeName, val means: String):
  type T
  given LeanType[T] = new LeanType[T]:
    val ty: Ty = Ty.Sort(name)
    val declares: Declarations = Declarations.sort(Sort(name, means))

object Opaque:
  inline def apply(means: String): Opaque = new Opaque(TypeName(Source.valName), means)

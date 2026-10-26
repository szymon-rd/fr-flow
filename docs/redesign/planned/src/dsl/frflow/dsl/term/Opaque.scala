package frflow.dsl.term

import frflow.core.name.TypeName
import frflow.core.ty.Ty
import frflow.core.vocab.Sort
import frflow.dsl.build.Declarations


/** A domain type, open until a definition fixes it: `val User = Opaque("User", means)`, used as `User.T`. */
final class Opaque(val name: TypeName, val means: String):
  type T
  given LeanType[T] = new LeanType[T]:
    val ty: Ty = Ty.Sort(name)
    val declares: Declarations = Declarations.sort(Sort(name, means))

object Opaque:
  def apply(name: String, means: String): Opaque = new Opaque(TypeName(name), means)

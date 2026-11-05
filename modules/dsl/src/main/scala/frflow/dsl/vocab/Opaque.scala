package frflow.dsl.vocab

import cats.syntax.all.*
import frflow.core.name.{RelPath, TypeName}
import frflow.core.ty.Ty
import frflow.core.vocab.Sort
import frflow.dsl.build.{Declarations, Source}
import frflow.dsl.term.LeanType

/** A domain type, open until a definition fixes it, named as its val: `val User = Opaque(means)`, used as `User.T`;
  * `at`, the file it is written in.
  */
final class Opaque(val name: TypeName, val means: String, val at: RelPath):
  type T
  given LeanType[T] = new LeanType[T]:
    val ty: Ty = Ty.Sort(name)
    val declares: Declarations = Declarations.sort(Sort(name, means)) |+| Declarations.in(Some(at), name.value)

object Opaque:
  inline def apply(means: String): Opaque = new Opaque(TypeName(Source.valName), means, Source.here)

package frflow
package vocabulary

/** An abstract idea, known only through the claims and assumptions about it (`authorized`): never called by code or a
  * flow, never implemented. The knowledge base is consistent only if some meaning of it meets them all: a witness,
  * derived from a claim that says what it equals.
  */
final class Declaration[A] @scala.annotation.publicInBinary private[frflow] (named: String, meaning: String)(using
    t: LeanType[A] = LeanType.unknown[A]) extends Param[A](named, meaning)

object Declaration:
  /** `val authorized = Declaration[(User, Doc) => Boolean]("whether the user may read the document")`. */
  inline def apply[A](means: String)(using t: LeanType[A] = LeanType.unknown[A]): Declaration[A] =
    new Declaration[A](Source.paramName, means)

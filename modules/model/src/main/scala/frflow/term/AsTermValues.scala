package frflow
package term

import scala.util.NotGiven

private[frflow] trait AsTermValues:
  given value[A](using t: LeanType[A], notTerm: NotGiven[A <:< Term[?]]): (AsTerm[A] { type R = A }) =
    new AsTerm[A] { type R = A; def apply(e: A) = Term.lit(e) }

package frflow.dsl.term

import frflow.core.expr.Lambda
import frflow.core.name.DefName
import frflow.core.spec.Written
import frflow.dsl.build.Deferred

/** A named function of the domain (`val matches = define { (q: Term[Query], r: Term[Record]) => … }`), named as its
  * val by the `define` macro. `F` is its Scala type; plain code runs it with `matches.fn(q, r)` (`eval.DefSyntax`).
  */
final class Def[F](val name: DefName, val lambda: Deferred[Written[Lambda]]):
  val compiled: Once[AnyRef] = Once()

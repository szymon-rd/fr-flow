package frflow.eval.flow

import frflow.*

/** A program of the tests over the shelf and the clock, a `Flow` as a model writes one; the faults its shelf's calls
  * take (`true`: that call fails), and what it gives on the models from an empty shelf at time 0: its outcome
  * (`Left` its error), the shelf, the time.
  */
final case class Shelved[R](name: String, faults: List[Boolean], expected: (Either[Any, Any], List[BigInt], BigInt))(
    val program: Flow[R])

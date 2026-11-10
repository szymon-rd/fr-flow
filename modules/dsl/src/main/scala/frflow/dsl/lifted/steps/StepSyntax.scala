package frflow.dsl.lifted.steps

/** `updating { (port: P^, input: A) => … }`: direct-style Scala over a port it has to itself (Scala's separation
  * checking says so: `P` is a `caps.Mutable` class, the parameter exclusive), read into a function of the port's
  * state (`StepReader`).
  */
object StepSyntax:
  inline def updating[P, A, R](inline f: (P, A) => R)(using s: PortState[P]): Updating[P, s.S, A, R] =
    ${ StepReader.updating[P, s.S, A, R]('f) }

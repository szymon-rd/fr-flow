package frflow.dsl.lifted.steps

import frflow.dsl.lifted.Lifted
import frflow.dsl.service.ServiceDeclaration
import frflow.dsl.term.Term
import frflow.dsl.vocab.Definition

/** A service method that changes a port, in direct style, read two ways (`StepReader`), each a function of the
  * port's state `S`. A port is a store (a class of Scala's `caps.Mutable`: `S` is its one `var`'s type) or a
  * service, a class holding ports (`S` is its one port's state, or, of several, the case class its companion
  * names: `type State = …`, a field per port).
  *
  *   - `updating { (service: Transfers^, t: Transfer) => service.transfer(t) }`: alone. From the state, its result
  *     with the state after it. Lifted code: its Scala is the method run on ports made from the state.
  *   - `interleaving { … }(others)`: among other calls. Before each of its calls of a store but the first, the
  *     others may have left any state the rely `others(input, before, after)` admits; `between` says which, by the
  *     call's number. Its result, with each state a call of a store started from and the state it left. A claim
  *     of it over every `between` holds however the method's steps interleave with other calls'.
  *
  * A call of a method of a port the code holds is a call of the Definition of the method's name in that port's
  * companion (`object Ledger { val claim = Definition[(Books, String) => (Boolean, Books)]("…") }`), when there
  * is one: the code's claims are then proven from the port's contracts, and the port's own code (`updating` over
  * the port itself, its methods' bodies) is given that word with `define`. Read alone that is so of
  * stores and of services; read among other calls, of stores, a service's method being its steps.
  */
object StepSyntax:
  inline def updating[P, A, R](inline f: (P, A) => R)(using s: PortState[P]): Lifted.Of2[s.S, A, (R, s.S)] =
    ${ StepReader.updating[P, s.S, A, R]('f) }

  inline def interleaving[P, A, R](inline f: (P, A) => R)(using s: PortState[P])(
      inline others: Lifted.Of3[A, s.S, s.S, Boolean])
      : Definition[(s.S, Map[BigInt, s.S], A) => (R, List[(s.S, s.S)])] =
    ${ StepReader.interleaving[P, s.S, A, R]('f, 'others) }

  /** `lifted(SpendLimits(BigInt(100), Nil))`: a class that implements a service, read member by member: what a
    * service's Definition is given (`limits.define(lifted(…))`), each member checked against every
    * claim on it (`ServiceLift`).
    */
  inline def lifted[C](inline service: C): ServiceImplementation[C] = ${ ServiceLift.read[C]('service) }

  extension [T](service: ServiceDeclaration[T])
    /** The service as an object of a class that implements it has it, for an example
      * (`limits.holding(SpendLimits(BigInt(100), Nil))`): the object made where it is given.
      */
    inline def holding(inline made: T): Term[service.Is] = ${ ServiceLift.held[T, service.Is]('made) }

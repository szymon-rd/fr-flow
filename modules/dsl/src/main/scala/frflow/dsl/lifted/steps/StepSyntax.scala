package frflow.dsl.lifted.steps

import frflow.dsl.lifted.Lifted
import frflow.dsl.vocab.Definition

/** A service method that changes a port (a store, a class of Scala's `caps.Mutable`, or a service holding one), in
  * direct style, read two ways (`StepReader`), each a function of the store's state `S`:
  *
  *   - `updating { (service: Transfers^, t: Transfer) => service.transfer(t) }`: alone. From the state, its result
  *     with the state after it. Lifted code: its Scala is the method run on a port made from the state.
  *   - `interleaving { … }(others)`: among other calls. Before each of its calls of the store but the first, the
  *     others may have left any state the rely `others(input, before, after)` admits; `between` says which, by the
  *     call's number. Its result, with each state a call of the store started from and the state it left. A claim
  *     of it over every `between` holds however the method's steps interleave with other calls'.
  *
  * A service's call of a store's method is a call of the Definition of the method's name in the store's companion
  * (`object Ledger { val claim = Definition[(Books, String) => (Boolean, Books)]("…") }`), when there is one: the
  * service's claims are then proven from the store's contracts, and the store's own code (`updating` over the
  * store itself, its methods' bodies) is given the Definition with `implementProven`.
  */
object StepSyntax:
  inline def updating[P, A, R](inline f: (P, A) => R)(using s: PortState[P]): Lifted.Of2[s.S, A, (R, s.S)] =
    ${ StepReader.updating[P, s.S, A, R]('f) }

  inline def interleaving[P, A, R](inline f: (P, A) => R)(using s: PortState[P])(
      inline others: Lifted.Of3[A, s.S, s.S, Boolean])
      : Definition[(s.S, Map[BigInt, s.S], A) => (R, List[(s.S, s.S)])] =
    ${ StepReader.interleaving[P, s.S, A, R]('f, 'others) }

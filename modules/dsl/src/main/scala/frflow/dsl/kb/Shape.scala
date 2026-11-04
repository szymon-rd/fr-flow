package frflow.dsl.kb

/** What an operation on a state is, as `implementTested(ops*)` reads its Definition's type at compile time
  * (`TestedMacro`): its inputs and result, one type per number of inputs. The plain Scala given it is a function of
  * its inputs to its result in the effect (`Shape.Scala`). Types only: no value of them is made.
  */
object Shape:
  final class Op0[R]
  final class Op1[A, R]
  final class Op2[A, B, R]
  final class Op3[A, B, C, R]
  final class Op4[A, B, C, D, R]
  final class Op5[A, B, C, D, E, R]
  final class Op6[A, B, C, D, E, F, R]
  /** A Definition that is no operation on a state: no Scala can be given it with the operations. */
  final class NotAnOperation[D]

  /** The plain Scala an operation of this shape is given, its result in `G`: `G[R]` of none, `A => G[R]` of one. */
  type Scala[S, G[_]] = S match
    case Op0[r]                   => G[r]
    case Op1[a, r]                => a => G[r]
    case Op2[a, b, r]             => (a, b) => G[r]
    case Op3[a, b, c, r]          => (a, b, c) => G[r]
    case Op4[a, b, c, d, r]       => (a, b, c, d) => G[r]
    case Op5[a, b, c, d, e, r]    => (a, b, c, d, e) => G[r]
    case Op6[a, b, c, d, e, f, r] => (a, b, c, d, e, f) => G[r]
    case NotAnOperation[d]        => NotAnOperation[d]

  /** Each operation's plain Scala, in order. */
  type Scalas[Ss <: Tuple, G[_]] = Tuple.Map[Ss, [s] =>> Scala[s, G]]

package frflow.eval.flow

import frflow.*

/** What a program over the shelf fails with: the shelf is down, or a number is too big. */
enum Trouble derives LeanType:
  case Down
  case TooBig(n: BigInt)

package frflow.core.vocab

import frflow.core.name.DefName

/** What kind of function a define is. */
enum DefineForm:
  case Function
  /** A flow's code: a generic `do` block over the boundaries' classes. */
  case Flow
  /** The run of a flow on the models (`f_run`: `FrFlow.runOn (f a) w`), what its contract's `impl` is proven of. */
  case RunOf(flow: DefName)

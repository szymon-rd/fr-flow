package frflow.core.expr

import frflow.core.name.{BoundaryName, DefName, ModelName, SymbolName}

/** What an assumption about the world outside the code says (owner §16: the company's procedures, the outside
  * services and how they are run). Lean's model of the world is built on these, so Lean states none of them as a
  * formula; each is the premise of the rule it lets FrFlow use (`analysis.Premises`).
  */
enum OutsideFact:
  /** The store does what its model does: code calling it is proven on the model, its code tested against it. */
  case BehavesAs(boundary: BoundaryName, model: ModelName)
  /** Only these programs change the model's state: every state it reaches is one they leave. */
  case WrittenOnlyBy(model: ModelName, programs: List[SymbolName])
  /** Runs changing the model's state never interleave: one process with `atomically`, or a store serializing them
    * (owner §17: each run is one step).
    */
  case OneRunAtATime(model: ModelName)
  /** What the model's state meets when the service starts (`stored.initially(held => held === Nil)`): its rule a
    * define named as the assumption.
    */
  case Initially(model: ModelName, rule: DefName)
  /** The world outside calls this Definition with values that can be made: each meets every `always[T]` of its type
    * (values entering from outside, owner §16).
    */
  case Calls(definition: SymbolName)

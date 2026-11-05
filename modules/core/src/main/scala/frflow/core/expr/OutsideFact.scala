package frflow.core.expr

import frflow.core.name.{DefName, ModelName}

/** What an assumption about the world outside the code says (owner §16: the company's procedures, the outside
  * services and how they are run), each said of a model (owner §36). Lean's model of the world is built on these, so
  * Lean states none of them as a formula; each is the premise of the rule it lets FrFlow use (`analysis.Premises`).
  * What values from outside meet is not one of them: it is an assumption of `always` on their type (owner §21), a
  * hypothesis Lean states. That the operations' plain Scala does what the model says is not assumed: it is tested.
  */
enum OutsideFact:
  /** Nothing outside the code changes the model's state (owner §31, §36): every state it reaches is one a run of the
    * programs changing it leaves (those FrFlow derives, `Premises.writers`).
    */
  case OnlyCodeChanges(model: ModelName)
  /** Runs on the state never interleave: one process with `atomically`, or a store serializing them (owner §17,
    * §32, §36: each run is one step of the world); and each call of the model's operations is one step against
    * calls at once, which the model tests check of its Scala.
    */
  case Atomic(model: ModelName)
  /** What the model's state meets when the service starts (`stored.initially(held => held === Nil)`): its rule a
    * define named as the assumption.
    */
  case Initially(model: ModelName, rule: DefName)
  /** Where the world moves the clock's time between runs (owner §47: a schedule, a trusted fact restricting the
    * outside steps): its own step (`elapse`) only to a time `rule` allows, given the states of `over` then
    * (`clockModel.schedule(lastRun)((now, ran) => now <= ran + 120)`: housekeeping runs at least every two minutes).
    * Inside a run the world moves the time freely, by any amount at any of the clock's steps and by at least its
    * seconds at a wait: other runs at once change what the schedule reads while a run is in progress, which that
    * run's view does not see (the step 13d review's B1).
    */
  case Schedule(model: ModelName, over: List[ModelName], rule: DefName)

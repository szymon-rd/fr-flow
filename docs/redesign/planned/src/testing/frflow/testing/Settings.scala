package frflow.testing

/** How many cases each node's code is tested on, from which seed: the checker's configuration (`project.Config`),
  * since it says how tests run, not what the model states.
  */
final case class Settings(cases: Int, seed: Seed)

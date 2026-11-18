package frflow.api.view

/** The system the nodes are about: the model's name, and what it is in a sentence or two when the model says. Not a
  * node: nothing checks it and nobody decides it; the front ends show it as the root everything hangs from.
  */
final case class SystemView(name: String, about: Option[String])

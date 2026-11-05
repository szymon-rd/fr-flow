package frflow.api.view

/** Why a class of examples found among a project's test classes could not be made, so none of its examples is read
  * (`Warning.ExamplesNotRead`): it has no constructor without arguments (a Scala default argument is not one), it is
  * nested in a class (its constructor takes the enclosing instance), it is anonymous, or making it threw.
  */
enum NotMade:
  case NoConstructor, Nested, Anonymous
  case Threw(message: String)

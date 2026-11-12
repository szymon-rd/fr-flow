package frflow.dsl.structure

import scala.quoted.Expr

/** What a reading knows of structures (`lifted.Reader`), when it reads a class that implements one
  * (`compiled.steps.ClassCode`): the record that class's state is, by its structure's name (`records`); for each
  * of the class's fields that is a structure, the Declaration it was made with, by the field's name (`wiring`): a
  * call of that field's member is a call of that Declaration's; and the traits the reading has as structures, by
  * name (`traits`): the one the class implements and those it holds. A trait that is one of Scala's
  * `caps.Mutable` is a structure in any reading; one that is not is a structure only where it is in play.
  */
final case class Structures(records: Map[String, Expr[Any]], wiring: Map[String, Expr[Any]], traits: Set[String])

object Structures:
  val none: Structures = Structures(Map.empty, Map.empty, Set.empty)

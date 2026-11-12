package frflow.dsl.service

import scala.quoted.Expr

/** What a reading knows of services (`lifted.Reader`), when it reads a class that implements one
  * (`lifted.steps.ServiceLift`):
  * the record that class's state is, by its service's name (`records`), and, for each of the class's fields that
  * is a service, the Definition it was made with, by the field's name (`wiring`): a call of that field's member is
  * a call of that Definition's.
  */
final case class Services(records: Map[String, Expr[Any]], wiring: Map[String, Expr[Any]])

object Services:
  val none: Services = Services(Map.empty, Map.empty)

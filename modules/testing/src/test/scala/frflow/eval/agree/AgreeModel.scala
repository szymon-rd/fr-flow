package frflow.eval.agree

import frflow.*
import scala.annotation.experimental

/** Each class of `Pure` and `Stateful` as the Definition of a structure. The code is what is checked here, against
  * the JVM (`AgreeExamples`); the one claim is there because a model has a root.
  */
@experimental object AgreeModel:
  import Pure.*
  import Stateful.*

  val arith = Declaration[Arith]("numbers and truth values")
  val tariff = Declaration[Tariff]("what sending a parcel costs: records and enums")
  val maybe = Declaration[Maybe]("options")
  val lists = Declaration[Lists]("lists")
  val tables = Declaration[Tables]("maps and sets, and pairs")
  val journal = Declaration[Journal]("the journal of the parcels taken")
  val depot = Declaration[Depot]("the depot: it takes parcels into its journal, at its tariff's price")

  val orderedOfOne = Node.claim("A number is in order with itself.")(
    forall((a: Term[BigInt]) => arith.ordered(a, a, a)))

  val model: FrModel = FrModel("Agree")(orderedOfOne, arith.define(lifted[PlainArith]),
    tariff.define(lifted[ZoneTariff]), maybe.define(lifted[PlainMaybe]), lists.define(lifted[PlainLists]),
    tables.define(lifted[PlainTables]), journal.define(lifted[ListJournal]),
    depot.define(lifted[TariffDepot](journal, tariff)))

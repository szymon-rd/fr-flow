package frflow.dsl.structure

import frflow.dsl.kb.FrModel
import frflow.dsl.kb.Defining.*
import frflow.dsl.lifted.steps.StepSyntax.lifted
import frflow.dsl.node.Node
import frflow.dsl.term.Term
import frflow.dsl.term.TermSyntax.*
import frflow.dsl.structure.Declaring as Declaration
import scala.annotation.experimental

/** A structure's Definition, and claims on it through its members. */
@experimental object TillModel:
  import Till.{CashTill, Sale, Till}

  val till = Declaration[Till]("the till: it takes each sale once")

  val takenIsRecorded = Node.claim("A sale taken is recorded.")(
    forall((s: Term[Sale]) => till.taken(s.id).in(till.take(s).after)))

  val takenOnce = Node.claim("A sale is taken exactly when it was not taken before.")(
    forall((s: Term[Sale]) => till.take(s).result === !till.taken(s.id).current))

  val takingAddsItsAmount = Node.claim("A sale taken adds its amount to the total.")(
    forall((s: Term[Sale]) =>
      till.take(s).result implies (till.total.in(till.take(s).after) === till.total + s.amount)))

  val noStepForgetsASale = Node.claim("No step of taking a sale forgets a sale taken, whatever other calls do " +
      "between the steps.")(
    forall((id: Term[SaleId], s: Term[Sale]) =>
      till.take(s).amongOthers(run => run.steps.forall(step =>
        till.taken(id).in(step._1) implies till.taken(id).in(step._2)))))

  val model: FrModel = FrModel("Tills")(takenIsRecorded, takenOnce, takingAddsItsAmount, noStepForgetsASale)
    .defining(till.define(lifted[CashTill]))

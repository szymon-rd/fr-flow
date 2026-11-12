package frflow.dsl.service

import frflow.dsl.kb.FrModel
import frflow.dsl.kb.Implementing.*
import frflow.dsl.lifted.LiftSyntax.lifted
import frflow.dsl.node.Node
import frflow.dsl.term.Term
import frflow.dsl.term.TermSyntax.*
import frflow.dsl.vocab.Definition
import scala.annotation.experimental

/** A service's Definition, and claims on it through its members. */
@experimental object TillModel:
  import Till.{CashTill, Sale, Till}

  val till = Definition[Till]("the till: it takes each sale once")

  val takenIsRecorded = Node.claim("A sale taken is recorded.")(
    forall((s: Term[Sale]) => till.taken(s.id).in(till.take(s).after)))

  val takenOnce = Node.claim("A sale is taken exactly when it was not taken before.")(
    forall((s: Term[Sale]) => till.take(s).result === !till.taken(s.id).current))

  val takingAddsItsAmount = Node.claim("A sale taken adds its amount to the total.")(
    forall((s: Term[Sale]) =>
      till.take(s).result implies (till.total.in(till.take(s).after) === till.total + s.amount)))

  val model: FrModel = FrModel("Tills")(takenIsRecorded, takenOnce, takingAddsItsAmount)
    .implementProven(till)(lifted(CashTill(Nil)))

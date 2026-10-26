package frflow.fixtures

import frflow.*

/** What always holds: of a book, and of a shelf, on the shelf's knowledge base; of the till's money, on the
  * service's.
  */
object Invariants:
  val hasPages = Node.claim("Every book has pages.")(always[Book](b => b.pages > 0))
  val shelvedOnce = Node.claim("No book is shelved twice.")(always[List[Book]](shelf => shelf.allDistinct))
  val shelf: KnowledgeBase = shelfWith(pick, hasPages, shelvedOnce)

  val notNegative = Node.claim("No amount is less than nothing.")(always[BigInt](x => x >= BigInt(0)))
  val service: KnowledgeBase =
    KnowledgeBase("Service", idea = "IDEA.md")(Service.sold, Service.pricePositive, Service.tillKept, notNegative)
      .implementProven(Service.sold)(Service.selling)
      .implementTested(Service.pricePositive)(item => item.abs + 1)

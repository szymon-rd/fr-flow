package payments

import frflow.*
import scala.util.chaining.*
import payments.Bank.{books, pay}

/** The promises: what Payments' users can rely on, each stated once, over the books and paying. How they are kept
  * is decided below them.
  */
object Payments:
  val ownerCanPay = Node.claim("A payable payment is made: its amount moves to the other account, and it is " +
      "recorded as paid.")(
    forall((p: Term[Payment]) =>
      Ledger.payable(books.current, p) implies Ledger.made(books.current, books.in(pay(p).after), p)))
    .assuming(Bank.oneAtATime)

  val neverBelowZero = Node.claim("No payment takes a balance below zero.")(
    forall((p: Term[Payment]) =>
      Ledger.noneNegative(books.current) implies Ledger.noneNegative(books.in(pay(p).after))))
    .assuming(Bank.oneAtATime)

  val moneyKept = Node.claim("No payment creates or loses money.")(
    forall((p: Term[Payment]) => Ledger.total(books.in(pay(p).after)) === Ledger.total(books.current)))
    .assuming(Bank.oneAtATime)

  val onlyOwnerPays = Node.claim("A payment not asked by the owner of the account it is from changes nothing.")(
    forall((p: Term[Payment]) =>
      !Ledger.owns(books.current, p.by, p.from) implies (books.in(pay(p).after) === books.current)))
    .assuming(Bank.oneAtATime)

  val paidOnce = Node.claim("A payment already made changes nothing when asked again.")(
    forall((p: Term[Payment]) =>
      Ledger.hasPaid(books.current, p.id) implies (books.in(pay(p).after) === books.current)))
    .assuming(Bank.oneAtATime)

  val othersUntouched = Node.claim("A payment changes no balance but those of its two accounts.")(
    forall((p: Term[Payment], id: Term[String]) => (id =!= p.from && id =!= p.to) implies
      (Ledger.balanceOf(books.in(pay(p).after), id) === Ledger.balanceOf(books.current, id))))
    .assuming(Bank.oneAtATime)

  /** Payments' FrModel: the system and every node. Lazy, because it names the nodes below the promises, which name
    * the promises.
    */
  lazy val model: FrModel = FrModel("Payments", "Users hold accounts with balances in whole cents and pay each " +
    "other.")(ownerCanPay, neverBelowZero, moneyKept, onlyOwnerPays, paidOnce, othersUntouched,
    Pay.payApplies, Pay.payRefuses, Books.idsStayDistinct, Bank.nothingElseWrites, Bank.oneAtATime,
    Bank.startsDistinct)
    .pipe(Bank.implemented).pipe(Ledger.generated)

package payments

import cats.syntax.all.*
import frflow.*

/** What the system keeps: every account with its balance, and the ids of the payments made. */
final case class Ledger(accounts: List[Account], paid: List[String]) derives LeanType

/** The words the ledger and payments are spoken of in. */
object Ledger:
  /** The balance of the account with this id; zero when there is none. */
  val balanceOf = define { (l: Term[Ledger], id: Term[String]) =>
    l.accounts.foldLeft(0: Term[BigInt])((sum, a) => when(a.id === id)(sum + a.balance).otherwise(sum)) }

  /** All the money held: the balances added up. */
  val total = define { (l: Term[Ledger]) => l.accounts.foldLeft(0: Term[BigInt])((sum, a) => sum + a.balance) }

  /** The user owns the account with this id. */
  val owns = define { (l: Term[Ledger], user: Term[String], id: Term[String]) =>
    l.accounts.exists(a => a.id === id && a.owner === user) }

  /** There is an account with this id. */
  val hasAccount = define { (l: Term[Ledger], id: Term[String]) => l.accounts.exists(a => a.id === id) }

  /** A payment with this id was made. */
  val hasPaid = define { (l: Term[Ledger], id: Term[String]) => l.paid.contains(id) }

  /** No balance is below zero. */
  val noneNegative = define { (l: Term[Ledger]) => l.accounts.forall(a => a.balance >= 0) }

  /** No two accounts share an id. */
  val distinctIds = define { (l: Term[Ledger]) => l.accounts.pairwise((a, b) => a.id =!= b.id) }

  /** A payment that can be made: asked by the owner of the account it is from, for a positive amount that account
    * covers, to another account, and not made before.
    */
  val payable = define { (l: Term[Ledger], p: Term[Payment]) =>
    owns(l, p.by, p.from) && p.amount > 0 && p.amount <= balanceOf(l, p.from) &&
      p.to =!= p.from && hasAccount(l, p.to) && !hasPaid(l, p.id) }

  /** From `before` to `after` the payment was made: its amount moved from the account it is from to the account it
    * is to, and it is recorded as paid.
    */
  val made = define { (before: Term[Ledger], after: Term[Ledger], p: Term[Payment]) =>
    balanceOf(after, p.from) === balanceOf(before, p.from) - p.amount &&
      balanceOf(after, p.to) === balanceOf(before, p.to) + p.amount && hasPaid(after, p.id) }

  /** The payment applied: its amount moved from the account it is from to the account it is to, and its id kept. */
  val applied = define { (l: Term[Ledger], p: Term[Payment]) =>
    make[Ledger](l.accounts.map(a =>
      when(a.id === p.from)(a.updated(_.balance, a.balance - p.amount))
        .otherwise(when(a.id === p.to)(a.updated(_.balance, a.balance + p.amount)).otherwise(a))),
      l.paid :+ p.id) }

  /** Ledgers the tests draw: three accounts of two owners, balances up to 50, a payment or none made. */
  val drawn: Gen[Ledger] = for
    a <- Gen.oneOf[BigInt](0, 5, 20, 50); b <- Gen.oneOf[BigInt](0, 10, 30); c <- Gen.oneOf[BigInt](0, 7)
    paid <- Gen.oneOf(List.empty[String], List("p1"))
  yield Ledger(List(Account("a", "ann", a), Account("b", "bob", b), Account("c", "ann", c)), paid)

  /** The ledgers and payments the tests draw. */
  def generated(model: FrModel): FrModel =
    model.withGenerator(drawn.describedAs("accounts a and c of ann, b of bob, balances up to 50, p1 made or not"))
      .withGenerator(Payment.drawn.describedAs("payments p1 or p2 by ann or bob between a, b, c and d, of -5 to 60"))

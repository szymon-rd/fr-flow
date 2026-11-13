package payments

import frflow.*

// The stream's data: the payments it reads from the log, and what its services keep of them.

/** A card payment as the log delivers it: its place in the log (`offset`), the id its sender gave it, the card it
  * charges, the merchant it pays, its amount, and the day it counts toward. The log may deliver a payment again
  * (the same offset), and a sender that heard nothing may have sent it twice (another offset, the same id).
  */
final case class Payment(offset: BigInt, id: PaymentId, card: CardId, merchant: MerchantId, amount: BigInt,
    day: BigInt)

object Payment:
  /** The amount is positive: the gateway refuses any other before it reaches the log. */
  given FrSpec[Payment] = FrSpec.derived[Payment].where(p => p.amount > 0)

/** What was decided of a payment: approved, or declined for the card's limit on that day. */
final case class Decision(id: PaymentId, card: CardId, day: BigInt, amount: BigInt, approved: Boolean)
    derives FrSpec

/** An account in the books: a card's, or a merchant's. */
enum Account derives FrSpec:
  case OfCard(card: CardId)
  case OfMerchant(merchant: MerchantId)

/** One side of a payment: an account's balance changed by an amount (negative: charged). */
final case class Posting(payment: PaymentId, account: Account, amount: BigInt) derives FrSpec

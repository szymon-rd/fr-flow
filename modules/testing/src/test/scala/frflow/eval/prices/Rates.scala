package frflow.eval.prices

import frflow.FrSpec
import scala.annotation.experimental

/** A structure whose class matches on an enum and on an option: what delivering a parcel costs. */
@experimental object Rates:
  /** How a parcel reaches its buyer. */
  enum Delivery derives FrSpec:
    case Collected
    case Posted(fee: BigInt)
    case Courier(fee: BigInt, surcharge: BigInt)

  final case class Parcel(delivery: Delivery, voucher: Option[BigInt]) derives FrSpec

  /** Delivery rates: what delivering a parcel costs. */
  trait Rating:
    /** What the delivery costs, before any voucher. */
    def fee(parcel: Parcel): BigInt
    /** What is charged: the fee, less a voucher's worth, and with a voucher never below the least charge. */
    def charge(parcel: Parcel): BigInt
    /** Whether the parcel is brought to the buyer. */
    def brought(parcel: Parcel): Boolean
    /** The least that is charged against a voucher. */
    def least: BigInt

  final class ListedRates(val least: BigInt) extends Rating:
    def fee(parcel: Parcel): BigInt = parcel.delivery match
      case Delivery.Collected   => BigInt(0)
      case Delivery.Posted(fee) => fee
      case c: Delivery.Courier  => c.fee + c.surcharge

    def charge(parcel: Parcel): BigInt = parcel.voucher match
      case Some(worth) => if fee(parcel) - worth < least then least else fee(parcel) - worth
      case None        => fee(parcel)

    def brought(parcel: Parcel): Boolean = parcel.delivery match
      case Delivery.Collected => false
      case _                  => true

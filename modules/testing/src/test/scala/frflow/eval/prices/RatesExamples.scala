package frflow.eval.prices

import frflow.*
import scala.annotation.experimental

/** The rates at work with a least charge of 1: each case of a delivery, with and without a voucher. */
@experimental class RatesExamples extends FrFlowExamples(RatesModel.model):
  import Rates.{Delivery, ListedRates, Parcel}
  import RatesModel.rates

  private val listed = rates.holding(ListedRates(BigInt(1)))
  private val courier = Parcel(Delivery.Courier(6, 2), None)

  example("a parcel collected costs nothing and is not brought"):
    val collected = Parcel(Delivery.Collected, None)
    (rates.fee(collected).in(listed) is BigInt(0)) && (rates.brought(collected).in(listed) is false)

  example("a parcel posted costs its fee"):
    rates.fee(Parcel(Delivery.Posted(4), None)).in(listed) is BigInt(4)

  example("a courier's parcel costs the fee and the surcharge, and is brought"):
    (rates.charge(courier).in(listed) is BigInt(8)) && (rates.brought(courier).in(listed) is true)

  example("a voucher is taken off the fee"):
    rates.charge(courier.copy(voucher = Some(3))).in(listed) is BigInt(5)

  example("a voucher worth more than the fee leaves the least charge"):
    rates.charge(courier.copy(voucher = Some(20))).in(listed) is BigInt(1)

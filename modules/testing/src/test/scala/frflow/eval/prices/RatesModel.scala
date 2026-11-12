package frflow.eval.prices

import frflow.*
import scala.annotation.experimental

/** The delivery rates as a structure: a Declaration of its trait, defined by its class. */
@experimental object RatesModel:
  import Rates.{ListedRates, Parcel, Rating}

  val rates = Declaration[Rating]("the delivery rates: what delivering a parcel costs")

  val voucherLeavesTheLeast = Node.claim("Against a voucher, no less than the least charge is charged.")(
    forall((p: Term[Parcel]) => p.voucher.isDefined implies (rates.least <= rates.charge(p))))

  val noVoucherChargesTheFee = Node.claim("Without a voucher, the fee is charged.")(
    forall((p: Term[Parcel]) => !p.voucher.isDefined implies (rates.charge(p) === rates.fee(p))))

  val model: FrModel = FrModel("Rates")(voucherLeavesTheLeast, noVoucherChargesTheFee,
    rates.define(lifted[ListedRates]))

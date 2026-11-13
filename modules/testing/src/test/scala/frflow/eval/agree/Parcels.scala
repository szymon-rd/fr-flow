package frflow.eval.agree

import frflow.FrSpec
import scala.annotation.experimental

/** The data the code of `Pure` and `Stateful` is over: an enum whose cases have fields, and a record that holds
  * one.
  */
@experimental object Parcels:
  /** Where a parcel goes. */
  enum Zone derives FrSpec:
    case Local
    case Regional(km: BigInt)
    case Abroad(country: String, km: BigInt)

  final case class Parcel(id: String, weight: BigInt, zone: Zone, express: Boolean) derives FrSpec

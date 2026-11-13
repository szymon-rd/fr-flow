package frflow.eval.agree

import scala.annotation.experimental
import scala.util.Random

/** The inputs the code is run on: drawn from one seed, from small ranges, so that names and numbers meet (a parcel
  * of an id already taken, a weight at a limit) as often as they differ.
  */
@experimental final class Draws(seed: Long):
  import Parcels.{Parcel, Zone}
  private val random = Random(seed)
  private val names = Vector("tea", "oak", "elm", "far")

  def number: BigInt = BigInt(random.between(-3, 9))
  def distance: BigInt = BigInt(random.between(-5, 80))
  def name: String = names(random.nextInt(names.size))
  def option: Option[BigInt] = if random.nextInt(3) == 0 then None else Some(number)
  def numbers: List[BigInt] = List.fill(random.nextInt(4))(number)
  def zone: Zone = random.nextInt(3) match
    case 0 => Zone.Local
    case 1 => Zone.Regional(BigInt(random.between(1, 60)))
    case _ => Zone.Abroad(name, BigInt(random.between(40, 90)))
  def parcel: Parcel = Parcel(name, BigInt(random.between(0, 7)), zone, random.nextBoolean())
  def parcels: List[Parcel] = List.fill(random.nextInt(4))(parcel)
  def table: Map[String, BigInt] = names.filter(_ => random.nextBoolean()).map(_ -> number).toMap
  def tags: Set[String] = names.filter(_ => random.nextBoolean()).toSet

  /** `n` draws of what `one` draws. */
  def of[A](n: Int)(one: => A): List[A] = List.fill(n)(one)

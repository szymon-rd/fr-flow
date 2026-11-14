package frflow.core.threads

/** A piece of data as a Rocq file writes it: a constructor applied, a text, a number, a truth value, a list, an
  * option. What code is read into where the reading chooses nothing (`dsl.compiled.source`): the constructors are
  * those of the Rocq type the data is of, which Rocq checks when it reads the file.
  */
enum Datum:
  case Of(constructor: String, args: List[Datum])
  case Text(value: String)
  case Nat(value: Int)
  case Whole(value: BigInt)
  case Truth(value: Boolean)
  case Many(elems: List[Datum])
  case Maybe(value: Option[Datum])

  /** How many constructors it applies, itself and inside it. */
  def size: Int = this match
    case Of(_, args)  => 1 + args.map(_.size).sum
    case Many(elems)  => elems.map(_.size).sum
    case Maybe(value) => value.fold(0)(_.size)
    case _            => 0

  /** The constructors it applies, each as often as it does. */
  def constructors: List[String] = this match
    case Of(c, args)  => c :: args.flatMap(_.constructors)
    case Many(elems)  => elems.flatMap(_.constructors)
    case Maybe(value) => value.toList.flatMap(_.constructors)
    case _            => Nil

object Datum:
  def of(constructor: String, args: Datum*): Datum = Of(constructor, args.toList)
  def texts(values: List[String]): Datum = Many(values.map(Text(_)))

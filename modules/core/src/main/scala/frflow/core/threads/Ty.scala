package frflow.core.threads

/** A type of the Rocq a thread program is written in (`modules/proof/rocq/FrFlow/Threads`): a named type (`nat`,
  * `tid`, `exn`, `val`, a class read), a type applied (`option T`, `list T`), a product or a sum.
  */
enum Ty:
  case Named(name: String)
  case Of(ctor: String, arg: Ty)
  case Prod(parts: List[Ty])
  case Sum(left: Ty, right: Ty)

  /** The named types this type is made of. */
  def names: List[String] = this match
    case Named(n)  => List(n)
    case Of(_, a)  => a.names
    case Prod(ps)  => ps.flatMap(_.names)
    case Sum(l, r) => l.names ++ r.names

object Ty:
  val Nat: Ty = Named("nat")
  val Tid: Ty = Named("tid")
  val Exn: Ty = Named("exn")
  val Val: Ty = Named("val")
  val Bool: Ty = Named("bool")
  val Unit: Ty = Named("unit")
  val Z: Ty = Named("Z")
  val Code: Ty = Named("code")
  /** The type of what never returns (a `throw`): a program of it is a program of any type. */
  val Never: Ty = Named("Empty_set")

  def option(of: Ty): Ty = Of("option", of)
  def list(of: Ty): Ty = Of("list", of)

  /** The type of several values held together: none is `unit`, one is itself. */
  def tuple(parts: List[Ty]): Ty = parts match
    case Nil      => Unit
    case List(of) => of
    case several  => Prod(several)

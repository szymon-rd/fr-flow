package frflow.dsl.lifted

import frflow.core.name.TypeName
import frflow.core.ty.Ty
import frflow.dsl.build.{Declarations, Source}
import frflow.dsl.term.{LeanType, Term}
import scala.annotation.implicitNotFound
import scala.deriving.Mirror

/** What a Scala type is to the Scala FrFlow reads (`lifted { … }`): its place in the term language (it is the type's
  * `LeanType`), and its contract, the rule every value of the type meets, written in Scala over the type's members
  * (`where`). Every type a value of lifted code has must have one: the standard types' are given here; a case class
  * or an enum derives its own (`derives FrSpec`), or gives it in its companion with its contract
  * (`given FrSpec[Booking] = FrSpec.derived[Booking].where(b => b.start < b.end)`). A node states the contract
  * (`contractOf[Booking]`): an assumption of a type from outside, a claim of one the code makes.
  *
  * Laws: `where` and `whereStated` change the contract only (`ty`, `declares` and `fields` stay the type's); a spec
  * made by `derived`, or given here, has no contract.
  */
@implicitNotFound("FrFlow: ${A} is used in lifted code but has no FrSpec: add `derives FrSpec` to its declaration, " +
  "or give one in its companion (`given FrSpec[…] = FrSpec.derived[…].where(v => …)`). Scala's Int and Long have " +
  "none (they wrap around; Lean's numbers do not): use BigInt")
final class FrSpec[A] private (of: LeanType[A], val contract: Option[Contract[A]]) extends LeanType[A]:
  def ty: Ty = of.ty
  def declares: Declarations = of.declares
  override def fields: List[LeanType.Field[A, ?]] = of.fields

  /** The same type, every value of it meeting `rule`: plain Scala over the value's members, read into a term
    * (`Reader`) and kept as the Scala it is.
    */
  inline def where(inline rule: A => Boolean): FrSpec[A] =
    ruled(Contract.Plain(LiftMacro.read1[A, Boolean](rule), rule, Source.of(rule)))

  /** The same, the rule written with the DSL: what plain Scala cannot say (`forall`, `exists`). */
  inline def whereStated(inline rule: Term[A] => Term[Boolean]): FrSpec[A] =
    ruled(Contract.Stated(rule, Source.of(rule)))

  /** What `where` and `whereStated` make: a spec has one contract, the last given. */
  def ruled(c: Contract[A]): FrSpec[A] = new FrSpec(of, Some(c))

  /** Whether `a` meets the contract, where it is plain Scala; a value of a type with none, or with one only Lean
    * reads, meets it.
    */
  def holds(a: A): Boolean = contract match
    case Some(Contract.Plain(_, native, _)) => native(a)
    case _                                  => true

object FrSpec:
  def apply[A](using s: FrSpec[A]): FrSpec[A] = s

  /** A type's spec with no contract: every value of the type is one that can occur. */
  def of[A](t: LeanType[A]): FrSpec[A] = new FrSpec(t, None)

  /** A case class's or an enum's, derived where it is declared (`derives FrSpec`), as its `LeanType` is; refused
    * of a type that declares its own `equals` (lifted code's `==` is data's).
    */
  inline def derived[T](using Mirror.Of[T]): FrSpec[T] =
    LiftMacro.structural[T]
    of(LeanType.derived[T])

  /** A type known by its name alone (a service's: its fields are those of the class given for it). */
  def named[A](name: String): FrSpec[A] = of(LeanType.of[A](Ty.Data(TypeName(name))))

  /** A pair's, a list's and a map's spec from their parts', said outright where a part has no given (a service's),
    * typed by what the reading that asks knows them as.
    */
  def pair[R](a: FrSpec[?], b: FrSpec[?]): FrSpec[R] = both[Any, Any](a.asInstanceOf[FrSpec[Any]],
    b.asInstanceOf[FrSpec[Any]]).asInstanceOf[FrSpec[R]]
  def list[R](a: FrSpec[?]): FrSpec[R] = many[Any](a.asInstanceOf[FrSpec[Any]]).asInstanceOf[FrSpec[R]]
  def map[R](k: FrSpec[?], v: FrSpec[?]): FrSpec[R] = keyed[Any, Any](k.asInstanceOf[FrSpec[Any]],
    v.asInstanceOf[FrSpec[Any]]).asInstanceOf[FrSpec[R]]

  private def both[A, B](a: FrSpec[A], b: FrSpec[B]): FrSpec[(A, B)] =
    given FrSpec[A] = a
    given FrSpec[B] = b
    summon[FrSpec[(A, B)]]

  private def many[A](a: FrSpec[A]): FrSpec[List[A]] =
    given FrSpec[A] = a
    summon[FrSpec[List[A]]]

  private def keyed[K, V](k: FrSpec[K], v: FrSpec[V]): FrSpec[Map[K, V]] =
    given FrSpec[K] = k
    given FrSpec[V] = v
    summon[FrSpec[Map[K, V]]]

  given FrSpec[Boolean] = of(LeanType[Boolean])
  given FrSpec[BigInt] = of(LeanType[BigInt])
  given FrSpec[String] = of(LeanType[String])
  given FrSpec[Unit] = of(LeanType[Unit])
  given [A](using a: FrSpec[A]): FrSpec[List[A]] = of(LeanType[List[A]])
  given [A](using a: FrSpec[A]): FrSpec[Option[A]] = of(LeanType[Option[A]])
  given [A](using a: FrSpec[A]): FrSpec[Set[A]] = of(LeanType[Set[A]])
  given [K, V](using k: FrSpec[K], v: FrSpec[V]): FrSpec[Map[K, V]] = of(LeanType[Map[K, V]])
  given [A, B](using a: FrSpec[A], b: FrSpec[B]): FrSpec[(A, B)] = of(LeanType[(A, B)])
  given [A, B](using a: FrSpec[A], b: FrSpec[B]): FrSpec[Either[A, B]] = of(LeanType[Either[A, B]])

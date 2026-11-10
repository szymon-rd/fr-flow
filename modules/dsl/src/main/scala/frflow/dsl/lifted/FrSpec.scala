package frflow.dsl.lifted

import frflow.core.name.DefName
import frflow.core.ty.Ty
import frflow.dsl.build.{Declarations, Fault, Source, WrittenAt}
import frflow.dsl.node.AlwaysSyntax
import frflow.dsl.term.{LeanType, Notes, Term, Terms, TermSyntax}
import frflow.dsl.vocab.Definition
import scala.annotation.implicitNotFound
import scala.deriving.Mirror

/** What a Scala type is to the Scala FrFlow reads (`lifted { … }`): its place in the term language (it is the type's
  * `LeanType`), and its contract, the rule every value of the type meets, written in Scala over the type's members
  * (`where`). Every type a value of lifted code has must have one: the standard types' are given here; a case class
  * or an enum derives its own (`derives FrSpec`), or gives it in its companion with its contract
  * (`given FrSpec[Booking] = FrSpec.derived[Booking].where(b => b.start < b.end)`).
  *
  * Laws: `where` changes the contract only (`ty`, `declares` and `fields` stay the type's); a spec made by `derived`
  * or given here has no contract.
  */
@implicitNotFound("FrFlow: ${A} is used in lifted code but has no FrSpec: add `derives FrSpec` to its declaration, " +
  "or give one in its companion (`given FrSpec[…] = FrSpec.derived[…].where(v => …)`). Scala's Int and Long have " +
  "none (they wrap around; Lean's numbers do not): use BigInt")
final class FrSpec[A] private (of: LeanType[A], val contract: Option[Definition[A => Boolean]]) extends LeanType[A]:
  def ty: Ty = of.ty
  def declares: Declarations = of.declares
  override def fields: List[LeanType.Field[A, ?]] = of.fields

  /** The same type, every value of it meeting `rule`: plain Scala over the value's members, read into a term
    * (`Reader`) and kept as the Scala it is, so the rule can be run on a value too (`contract`'s `native`).
    */
  inline def where(inline rule: A => Boolean): FrSpec[A] =
    ruled(Lifted.Of1(Lifting.one[A, Boolean](FrSpec.contractName(Source.typeName[A]), WrittenAt.in(Source.here),
      Source.of(rule))(LiftMacro.read1[A, Boolean](rule))(using this, FrSpec[Boolean]), rule))

  /** The same, the rule written with the DSL: what plain Scala cannot say (`forall`, `exists`). */
  inline def whereStated(inline rule: Term[A] => Term[Boolean]): FrSpec[A] =
    ruled(Lifting.stated[A](FrSpec.contractName(Source.typeName[A]), WrittenAt.in(Source.here), Source.of(rule))(rule)(
      using this))

  /** Made by `where` and `whereStated` only: a spec has one contract. */
  def ruled(rule: Definition[A => Boolean]): FrSpec[A] = new FrSpec(of, Some(rule))

object FrSpec:
  def apply[A](using s: FrSpec[A]): FrSpec[A] = s

  /** A type's spec with no contract: every value of the type is one that can occur. */
  def of[A](t: LeanType[A]): FrSpec[A] = new FrSpec(t, None)

  /** A case class's or an enum's, derived where it is declared (`derives FrSpec`), as its `LeanType` is. */
  inline def derived[T](using Mirror.Of[T]): FrSpec[T] = of(LeanType.derived[T])

  /** `always` of a type's contract: a node's whole formula (an assumption of a type from outside, a claim of one
    * the code makes); of a type whose spec states none, a fault on the node.
    */
  def contractOf[A](using s: FrSpec[A]): Term[Boolean] = s.contract.fold(
    Term.noted(Notes.fault(Fault.NoContract(Ty.names(s.ty).headOption.fold(s.ty.toString)(_.value))))(TermSyntax.True.run))(rule =>
    Terms.always[A]("x", AlwaysSyntax.applied(rule)))

  /** The name of a type's contract, the define its rule is: `bookingContract` of `Booking`. */
  def contractName(scalaType: String): DefName =
    val simple = scalaType.split('.').last
    DefName(simple.take(1).toLowerCase + simple.drop(1) + "Contract")

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

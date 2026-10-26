package frflow.dsl.term

import cats.data.NonEmptyList
import cats.syntax.all.*
import frflow.core.code.DataRep
import frflow.core.name.{CtorName, TypeName}
import frflow.core.term.Case
import frflow.core.ty.{Ctor, DataType, Field, Ty}
import frflow.dsl.build.{Declarations, Declared}

/** The companion of a case class or an enum built from terms (`object Claims extends Data[Claims]`): its constructor
  * on terms (`Claims(r, u, rs)`, each argument checked against its field's type at compile time).
  */
trait Data[T]:
  transparent inline def apply(inline args: Term[?]*): Term[?] = ${ CaseMacros.make[T]('args) }

/** What `DataMacros` derives a domain type's `LeanType` from: its declaration, how Scala builds and takes apart its
  * values (`DataRep`), and its fields' selectors (a record's) or its cases (a sum's).
  */
object Data:
  /** A sum's case as derived: its name, its fields' names and `LeanType`s, its maker from the fields' values. */
  type Alt[T] = (String, List[(String, LeanType[?])], List[Any] => T)

  def product[T](scalaName: String, fields: List[LeanType.Field[T, ?]], make: List[Any] => T): LeanType[T] =
    val name = TypeName(scalaName.split('.').last)
    val data = DataType.Product(name, scalaName, fields.map(f => Field(f.selector.name, f.selector.ty)))
    val rep = DataRep((_, args) => make(args), a => (CtorName("mk"), parts(a)))
    declared(Declared(data, rep), fields.map(_.leanType), fields)

  /** A sum: its cases, and the case a value is (`ordinal`, by the sum's `Mirror`). */
  def sum[T](scalaName: String, cases: NonEmptyList[Alt[T]], ordinal: Any => Int): LeanType[T] =
    val name = TypeName(scalaName.split('.').last)
    val ctors = cases.map((c, fs, _) => Ctor(CtorName(c), fs.map((n, t) => Field(n, t.ty))))
    val makers = cases.toList.map((c, _, make) => CtorName(c) -> make).toMap
    val rep = DataRep((c, args) => makers(c)(args), a => (ctors.toList(ordinal(a)).name, parts(a)))
    declared(Declared(DataType.Sum(name, scalaName, ctors), rep), cases.toList.flatMap(_._2.map(_._2)), Nil)

  /** A case of a sum as an arm's variable has it: a value of the sum in Lean, its own fields in Scala. */
  def caseType[S, C](sum: LeanType[S], caseFields: List[LeanType.Field[C, ?]]): LeanType[C] = new LeanType[C]:
    val ty: Ty = sum.ty
    val declares: Declarations = sum.declares
    override val fields: List[LeanType.Field[C, ?]] = caseFields

  /** Case `label` of sum `S`, told by `test`. */
  def caseOf[S, C](sum: LeanType[S], label: String, fields: List[LeanType.Field[C, ?]], test: S => Option[C])
      : Case[S, C] =
    val name = sum.ty match
      case Ty.Data(n) => n
      case other      => throw IllegalStateException(s"FrFlow bug: a case of $other, which is not a sum")
    Case(name, CtorName(label), fields.map(f => f.selector.name -> f.selector.ty), test)

  private def declared[T](d: Declared, parts: List[LeanType[?]], fs: List[LeanType.Field[T, ?]]): LeanType[T] =
    new LeanType[T]:
      val ty: Ty = Ty.Data(d.data.typeName)
      val declares: Declarations = Declarations.of(d) |+| parts.foldMap(_.declares)
      override val fields: List[LeanType.Field[T, ?]] = fs

  private def parts(a: Any): List[Any] = a match
    case p: Product => p.productIterator.toList
    case _          => Nil // `DataRep` takes apart only values of its own type

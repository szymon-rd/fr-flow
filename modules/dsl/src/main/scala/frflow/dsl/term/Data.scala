package frflow.dsl.term

import cats.data.NonEmptyList
import cats.syntax.all.*
import frflow.core.code.DataRep
import frflow.core.name.{CtorName, TypeName}
import frflow.core.term.Case
import frflow.core.ty.{Ctor, DataType, Field, Ty}
import frflow.dsl.build.{Declarations, Declared, Source}

/** The companion of a case class or an enum built from terms (`object Claims extends Data[Claims]`): its constructor
  * on terms (`Claims(r, u, rs)`, each argument checked against its field's type at compile time).
  */
trait Data[T]:
  transparent inline def apply(inline args: Term[?]*): Term[?] = ${ CaseMacros.make[T]('args) }

/** What `DataMacros` derives a domain type's `RocqType` from: its declaration, how Scala builds and takes apart its
  * values (`DataRep`), and its fields' selectors (a record's) or its cases (a sum's).
  */
object Data:
  /** A sum's case as derived: its name, its fields' names and `RocqType`s, its maker from the fields' values. */
  type Alt[T] = (String, List[(String, RocqType[?])], List[Any] => T)

  def product[T](named: (String, Option[String]), fields: List[RocqType.Field[T, ?]], make: List[Any] => T)
      : RocqType[T] =
    val (scalaName, at) = named
    val name = TypeName(scalaName.split('.').last)
    val data = DataType.Product(name, scalaName, fields.map(f => Field(f.selector.name, f.selector.ty)))
    val rep = DataRep((_, args) => make(args), a => (CtorName("mk"), parts(a)))
    declared(Declared(data, rep), at, fields.map(_.rocqType), fields)

  /** A sum: its cases, and the case a value is (`ordinal`, by the sum's `Mirror`). */
  def sum[T](named: (String, Option[String]), cases: NonEmptyList[Alt[T]], ordinal: Any => Int): RocqType[T] =
    val (scalaName, at) = named
    val name = TypeName(scalaName.split('.').last)
    val ctors = cases.map((c, fs, _) => Ctor(CtorName(c), fs.map((n, t) => Field(n, t.ty))))
    val makers = cases.toList.map((c, _, make) => CtorName(c) -> make).toMap
    val rep = DataRep((c, args) => makers(c)(args), a => (ctors.toList(ordinal(a)).name, parts(a)))
    declared(Declared(DataType.Sum(name, scalaName, ctors), rep), at, cases.toList.flatMap(_._2.map(_._2)), Nil)

  /** A case of a sum as an arm's variable has it: a value of the sum in Rocq, its own fields in Scala. */
  def caseType[S, C](sum: RocqType[S], caseFields: List[RocqType.Field[C, ?]]): RocqType[C] = new RocqType[C]:
    val ty: Ty = sum.ty
    val declares: Declarations = sum.declares
    override val fields: List[RocqType.Field[C, ?]] = caseFields

  /** Case `label` of sum `S`, told by `test`. */
  def caseOf[S, C](sum: RocqType[S], label: String, fields: List[RocqType.Field[C, ?]], test: S => Option[C])
      : Case[S, C] =
    val name = sum.ty match
      case Ty.Data(n) => n
      case other      => throw IllegalStateException(s"FrFlow bug: a case of $other, which is not a sum")
    Case(name, CtorName(label), fields.map(f => f.selector.name -> f.selector.ty), test)

  /** A type's `RocqType`, declaring it, its parts' types, and the file it is written in (`at`). */
  private def declared[T](d: Declared, at: Option[String], parts: List[RocqType[?]], fs: List[RocqType.Field[T, ?]])
      : RocqType[T] =
    new RocqType[T]:
      val ty: Ty = Ty.Data(d.data.typeName)
      val declares: Declarations = Declarations.of(d) |+|
        Declarations.in(at.map(Source.path), d.data.typeName.value) |+|
        parts.foldMap(_.declares)
      override val fields: List[RocqType.Field[T, ?]] = fs

  private def parts(a: Any): List[Any] = a match
    case p: Product => p.productIterator.toList
    case _          => Nil // `DataRep` takes apart only values of its own type

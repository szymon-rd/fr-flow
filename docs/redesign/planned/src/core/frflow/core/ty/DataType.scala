package frflow.core.ty

import cats.data.NonEmptyList
import frflow.core.name.{CtorName, TypeName}

/** A domain type: a case class (a Lean `structure`) or an enum (an `inductive`), as Scala and Lean name it. */
enum DataType:
  case Product(name: TypeName, scalaName: String, fields: List[Field])
  case Sum(name: TypeName, scalaName: String, cases: NonEmptyList[Ctor])

  def typeName: TypeName = this match
    case Product(n, _, _) => n
    case Sum(n, _, _)     => n

  def isEnum: Boolean = this match
    case Product(_, _, _) => false
    case Sum(_, _, _)     => true

  /** The types of its fields, every constructor's. */
  def fieldTypes: List[Ty] = this match
    case Product(_, _, fs) => fs.map(_.ty)
    case Sum(_, _, cs)     => cs.toList.flatMap(_.fields.map(_.ty))

  /** The fields' types of one constructor (a case class has one). */
  def fieldsOf(c: CtorName): List[Ty] = this match
    case Product(_, _, fs) => fs.map(_.ty)
    case Sum(_, _, cs)     => cs.find(_.name == c).toList.flatMap(_.fields.map(_.ty))

  /** The domain types its fields name: declared before it in Lean. */
  def uses: List[TypeName] = fieldTypes.flatMap(Ty.names).distinct.filterNot(_ == typeName)

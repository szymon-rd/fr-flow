package frflow.dsl.lifted.steps

import cats.syntax.all.*
import frflow.core.code.DataRep
import frflow.core.name.{CtorName, TypeName}
import frflow.core.term.Selector
import frflow.core.ty.{DataType, Field, Ty}
import frflow.dsl.build.{Declarations, Declared, Source}
import frflow.dsl.lifted.FrSpec
import frflow.dsl.term.LeanType

/** What a structure's type is to the term language: a record named as the structure's trait, whose fields are those of
  * the class that implements it. A statement about the structure needs the name only (`FrSpec.named`); the class
  * brings the fields (`record`), declared with the class it is given (`limits.define(lifted[SpendLimits])`).
  */
object StructureType:
  /** A structure's state as the evaluator holds it: the values of its fields, equal when they are. An object of
    * the class that implements the structure is equal only to itself, so a state is never held as one.
    */
  final case class Held(structure: String, fields: List[Any])

  /** The record an implementation's state is: its constructor's fields. A value of it is a `Held`; an object of
    * the class is taken apart by reading its fields.
    */
  def record[T](named: (String, String, Option[String]), parts: List[LeanType.Field[T, ?]]): FrSpec[T] =
    val (name, scalaName, at) = named
    val names = parts.map(_.selector.name)
    val data = DataType.Product(TypeName(name), scalaName, parts.map(f => Field(f.selector.name, f.selector.ty)))
    val declared = Declared(data, DataRep((_, args) => Held(name, args), a => (CtorName("mk"), fieldsOf(a, names))))
    FrSpec.of(new LeanType[T]:
      val ty: Ty = Ty.Data(TypeName(name))
      val declares: Declarations = Declarations.of(declared) |+| Declarations.in(at.map(Source.path), name) |+|
        parts.foldMap(_.leanType.declares)
      override val fields: List[LeanType.Field[T, ?]] = parts)

  /** A state's fields' values, in order: a held state's, or an object's, read by name. */
  def fieldsOf(state: Any, names: List[String]): List[Any] = state match
    case Held(_, fields) => fields
    case made            => names.map(read(made, _))

  /** A field of an implementation's record: its name and place (`field`), in the record of a structure with its
    * fields' names (`of`).
    */
  def selector[S, F](field: (String, Int), of: (String, List[String]), ty: Ty): Selector[S, F] =
    val ((name, i), (structure, names)) = (field, of)
    Selector[S, F](name, i, TypeName(structure), ty, (state: S) => fieldsOf(state, names)(i).asInstanceOf[F],
      (state: S, v: F) => Held(structure, fieldsOf(state, names).updated(i, v)).asInstanceOf[S]) // held, not made

  /** An object of a class that implements a structure as a state the evaluator holds: its fields' values, an object
    * among them that implements a structure held the same way. A value of a domain type that is no case class is
    * such an object.
    */
  def held(spec: LeanType[?], structure: Any): Any =
    def of(ty: Ty, a: Any): Any = (ty, a) match
      case (Ty.Data(n), made) if !made.isInstanceOf[Product] =>
        spec.declares.types.get(n).flatMap(_.headOption).fold(made)(d =>
          Held(n.value, d.rep.split(made)._2.zip(d.data.fieldsOf(CtorName("mk"))).map((v, t) => of(t, v))))
      case _                                                 => a
    of(spec.ty, structure)

  /** A field of an implementation's object, read where Scala does not let code outside the class read it. */
  def read(of: Any, field: String): Any =
    val f = of.getClass.getDeclaredField(field)
    f.setAccessible(true)
    f.get(of)

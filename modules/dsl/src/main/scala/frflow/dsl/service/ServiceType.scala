package frflow.dsl.service

import cats.syntax.all.*
import frflow.core.code.DataRep
import frflow.core.name.{CtorName, TypeName}
import frflow.core.ty.{DataType, Field, Ty}
import frflow.dsl.build.{Declarations, Declared, Source}
import frflow.dsl.lifted.FrSpec
import frflow.dsl.term.LeanType

/** What a service's type is to the term language: a record named as the service's trait, whose fields are those of
  * the class that implements it. A statement about the service needs the name only (`named`); the class brings
  * the fields (`record`), declared with the implementation it is given (`implementProven`).
  */
object ServiceType:
  /** The service's type by its name: what a Definition of the service, and code that calls it, are typed by. */
  def named[T](name: String): FrSpec[T] = FrSpec.of(LeanType.of[T](Ty.Data(TypeName(name))))

  /** The record an implementation's state is: its constructor's fields, made by its constructor (`make`) and taken
    * apart by reading them (`split`).
    */
  def record[T](named: (String, String, Option[String]), parts: List[LeanType.Field[T, ?]])(
      make: List[Any] => T, split: Any => List[Any]): FrSpec[T] =
    val (name, scalaName, at) = named
    val data = DataType.Product(TypeName(name), scalaName, parts.map(f => Field(f.selector.name, f.selector.ty)))
    val declared = Declared(data, DataRep((_, args) => make(args), a => (CtorName("mk"), split(a))))
    FrSpec.of(new LeanType[T]:
      val ty: Ty = Ty.Data(TypeName(name))
      val declares: Declarations = Declarations.of(declared) |+| Declarations.in(at.map(Source.path), name) |+|
        parts.foldMap(_.leanType.declares)
      override val fields: List[LeanType.Field[T, ?]] = parts)

  /** A field of an implementation's record, by its place, typed as the reading has it. */
  def fieldOf[S, F](record: FrSpec[S], i: Int): LeanType.Field[S, F] =
    record.fields(i).asInstanceOf[LeanType.Field[S, F]]

  /** A field of an implementation's object, read where Scala does not let code outside the class read it. */
  def read(of: Any, field: String): Any =
    val f = of.getClass.getDeclaredField(field)
    f.setAccessible(true)
    f.get(of)

  /** A pair's, a list's and a map's spec from their parts': what a spec found by its type is, said outright where
    * a part is a service's (which has no given). Typed by what the reading that asks knows them as.
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

package frflow.dsl.lifted.steps

import frflow.core.name.TypeName
import frflow.core.term.Selector as FieldSelector
import frflow.dsl.build.Source
import frflow.dsl.lifted.{FrSpec, Reader}
import frflow.dsl.service.ServiceType
import frflow.dsl.term.LeanType
import scala.quoted.*

/** The record the state of a class that implements a service is (`ServiceLift`): named as the service, a field
  * for each of the class's constructor's, in order. A value of it is an instance of the class.
  */
private[steps] final class ServiceRecord(val r: Reader):
  import r.q.reflect.*

  def of[T: Type](implementing: Any, name: String)(using Quotes): Expr[FrSpec[T]] =
    val cls = implementing.asInstanceOf[Symbol]
    val fields = r.stateFields(cls)
    val file = cls.pos.map(p => Source.relative(p.sourceFile.path))
    '{ val make: List[Any] => T = (args: List[Any]) => ${ constructed[T](cls, fields, 'args) }
       ServiceType.record[T]((${ Expr(name) }, ${ Expr(cls.fullName) }, ${ Expr(file) }),
         ${ Expr.ofList(fields.zipWithIndex.map(field[T](cls, name, 'make))) })(
         make, (of: Any) => ${ parts(fields, 'of) }) }

  /** An instance made of its fields' values. */
  private def constructed[T: Type](cls: Symbol, fields: List[Symbol], args: Expr[List[Any]])(using Quotes): Expr[T] =
    Apply(Select(New(Inferred(cls.typeRef)), cls.primaryConstructor), fields.zipWithIndex.map((f, i) =>
      TypeApply(Select.unique('{ $args(${ Expr(i) }) }.asTerm, "asInstanceOf"),
        List(Inferred(cls.typeRef.memberType(f)))))).asExprOf[T]

  /** An instance's fields' values, in order. */
  private def parts(fields: List[Symbol], of: Expr[Any])(using Quotes): Expr[List[Any]] =
    Expr.ofList(fields.map(f => '{ ServiceType.read($of, ${ Expr(f.name) }) }))

  private def field[T: Type](cls: Symbol, name: String, make: Expr[List[Any] => T])(at: (Symbol, Int))(
      using Quotes): Expr[LeanType.Field[T, ?]] =
    val (f, i) = at
    r.stateOfType(cls.typeRef.memberType(f), cls.tree).asType match
      case '[x] =>
        val spec = r.spec[x](cls.tree)
        '{ LeanType.Field[T, x](FieldSelector[T, x](${ Expr(f.name) }, ${ Expr(i) }, TypeName(${ Expr(name) }),
          $spec.ty, (of: T) => ServiceType.read(of, ${ Expr(f.name) }).asInstanceOf[x],
          (of: T, v: x) => $make(${ parts(r.stateFields(cls), 'of) }.updated(${ Expr(i) }, v))), $spec) }

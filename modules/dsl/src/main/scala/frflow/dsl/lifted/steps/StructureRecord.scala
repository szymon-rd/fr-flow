package frflow.dsl.lifted.steps

import frflow.dsl.build.Source
import frflow.dsl.lifted.{FrSpec, Reader}
import frflow.dsl.term.LeanType
import scala.quoted.*

/** The record the state of a class that implements a structure is (`StructureLift`): named as the structure, a field
  * for each of the class's constructor's, in order.
  */
private[steps] final class StructureRecord(val r: Reader):
  import r.q.reflect.*

  def of[T: Type](implementing: Any, name: String)(using Quotes): Expr[FrSpec[T]] =
    val cls = implementing.asInstanceOf[Symbol]
    val fields = r.stateFields(cls)
    val file = cls.pos.map(p => Source.relative(p.sourceFile.path))
    '{ StructureType.record[T]((${ Expr(name) }, ${ Expr(cls.fullName) }, ${ Expr(file) }),
      ${ Expr.ofList(fields.zipWithIndex.map(field[T](cls, name, fields.map(_.name)))) }) }

  private def field[T: Type](cls: Symbol, name: String, names: List[String])(at: (Symbol, Int))(using Quotes)
      : Expr[LeanType.Field[T, ?]] =
    val (f, i) = at
    r.stateOfType(cls.typeRef.memberType(f), cls.tree).asType match
      case '[x] =>
        val spec = r.spec[x](cls.tree)
        '{ LeanType.Field[T, x](StructureType.selector[T, x]((${ Expr(f.name) }, ${ Expr(i) }),
          (${ Expr(name) }, ${ Expr(names) }), $spec.ty), $spec) }

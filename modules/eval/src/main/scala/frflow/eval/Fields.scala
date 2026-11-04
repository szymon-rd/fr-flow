package frflow.eval

import frflow.core.Elaborated
import frflow.core.name.{CtorName, TypeName}
import frflow.core.ty.{DataType, Ty}

/** The types of a constructor's fields, in order. */
object Fields:
  def of(e: Elaborated, n: TypeName, c: CtorName): List[Ty] =
    e.theory.vocabulary.dataType(n).toList.flatMap {
      case DataType.Product(_, _, fs) => fs.map(_.ty)
      case DataType.Sum(_, _, cs)     => cs.find(_.name == c).toList.flatMap(_.fields.map(_.ty))
    }

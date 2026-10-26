package frflow.dsl.build

import frflow.core.code.DataRep
import frflow.core.ty.DataType

/** A domain type a term needs declared: its declaration in the IR, and how Scala holds its values. */
final case class Declared(data: DataType, rep: DataRep)

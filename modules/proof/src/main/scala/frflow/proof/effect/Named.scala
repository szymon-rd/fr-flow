package frflow.proof.effect

import frflow.core.effect.{ClassName, FieldName, MethodName, OutsideName}

/** The names a generated program gives its classes, fields, methods and what it calls outside itself: each a
  * constructor of a type of the program's own, told from the others by its first letter.
  */
object Named:
  def cls(c: ClassName): String = "C_" + c.written
  def field(f: FieldName): String = "F_" + f.written
  def method(m: MethodName): String = "M_" + m.written
  def outside(o: OutsideName): String = "O_" + o.written

  /** The definition that is a method's tree. */
  def tree(m: MethodName): String = m.written

package frflow.proof.effect

import frflow.core.effect.{ClassName, FieldName, Idents, MethodName, OutsideName}

/** The names a generated program gives its classes, fields, methods and what it calls outside itself: each a
  * constructor of a type of the program's own, told from the others by its first letter.
  */
object Named:
  def cls(c: ClassName): String = "C_" + Idents.plain(c.value)
  def field(f: FieldName): String = s"F_${Idents.plain(f.cls.value)}_${Idents.plain(f.name)}"
  def method(m: MethodName): String = s"M_${Idents.plain(m.cls.value)}_${Idents.plain(m.name)}"
  def outside(o: OutsideName): String = s"O_${Idents.plain(o.owner)}_${Idents.plain(o.name)}"

  /** The definition that is a method's tree. */
  def tree(m: MethodName): String = s"${Idents.plain(m.cls.value)}_${Idents.plain(m.name)}"

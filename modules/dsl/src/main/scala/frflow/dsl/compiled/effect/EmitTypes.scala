package frflow.dsl.compiled.effect

import frflow.core.effect.EType

/** The type a value of the code has in a tree: Scala's `Int`, `Boolean` and `Unit` as themselves, an object of
  * any class as where it is. Any other type is refused: a tree has no value of it yet.
  */
private[effect] trait EmitTypes extends EmitBase:
  import q.reflect.*

  def ty(t: TypeRepr, at: Tree): EType =
    val is = t.widen.dealias
    if is =:= TypeRepr.of[Int] then EType.Int
    else if is =:= TypeRepr.of[Boolean] then EType.Bool
    else if is =:= TypeRepr.of[Unit] then EType.Unit
    else if isObject(is) then EType.Ref
    else refuse(s"a value of type ${is.show}", at)

  def isUnit(t: TypeRepr): Boolean = t.widen.dealias =:= TypeRepr.of[Unit]

  /** A type whose values are objects: a class that is no primitive of the JVM's, and no function. */
  private def isObject(t: TypeRepr): Boolean =
    val s = t.typeSymbol
    s.isClassDef && t <:< TypeRepr.of[AnyRef] && !t.isFunctionType && !(t =:= TypeRepr.of[Null])

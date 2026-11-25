package frflow.dsl.compiled.normal

import frflow.core.effect.EType

/** The type a value of the code has: Scala's `Int`, `Boolean` and `Unit` as themselves, an object of any class
  * as a reference. Any other type is refused: there is no value of it yet.
  */
private[normal] trait ReadTypes extends ReadBase:
  import q.reflect.*

  def ty(t: TypeRepr, at: Tree): EType =
    val is = strict(t, at).widen.dealias
    if is =:= TypeRepr.of[Nothing] then refuse("what gives no value", at)
    else if is <:< TypeRepr.of[Int] then EType.Int
    else if is <:< TypeRepr.of[Boolean] then EType.Bool
    else if is =:= TypeRepr.of[Unit] then EType.Unit
    else if isObject(is) then EType.Ref
    else refuse(s"a value of type ${is.show}", at)

  /** A type of values: one evaluated where it is written, once. What is passed by name, or several at once,
    * is none.
    */
  private def strict(t: TypeRepr, at: Tree): TypeRepr = t match
    case ByNameType(_)                                         => refuse("what is passed by name", at)
    case _ if t.typeSymbol == defn.RepeatedParamClass          => refuse("several values passed as one", at)
    case _                                                     => t

  def isUnit(t: TypeRepr): Boolean = t.widen.dealias =:= TypeRepr.of[Unit]

  /** A type whose values are objects: a class that is no primitive of the JVM's, and no function. */
  private def isObject(t: TypeRepr): Boolean =
    val s = t.typeSymbol
    s.isClassDef && t <:< TypeRepr.of[AnyRef] && !t.isFunctionType && !(t =:= TypeRepr.of[Null])

package frflow.code

import frflow.*
import frflow.executions.*
import frflow.values.{Obj, Value}
import scala.quoted.*

// Who reads and who writes the `val`s of an object, and that none has a data race. A plain write is two events,
// a mark and the write: a field is being written from the one to the other, and a race is a read, a mark or a
// write of it by another thread meanwhile (two accesses, one a write, that nothing orders: JLS 17.4.5).

extension [C](on: Obj[C])
  /** Each `val` of the object's class is marked and written only by the actor that makes the object, inside the
    * call that makes it.
    */
  inline def assignsItsValsWhereMade(using st: Stating): Term[Boolean] =
    ${ ValMacros.assigned[C]('on, 'st) }

  /** Each `val` of the object's class is read only by a call of a method of the class on the object, itself, or
    * by a call `also` says (of a function the object handed out): one made before the read.
    */
  inline def readsItsValsItself(also: (Term[Value], Moment) => Term[Boolean])(using st: Stating): Term[Boolean] =
    ${ ValMacros.readItself[C]('on, 'also, 'st) }

  /** Each `val` of the object's class is read only at a moment of which `holds`. */
  inline def readsItsValsOnlyWhen(holds: Moment => Term[Boolean])(using st: Stating): Term[Boolean] =
    ${ ValMacros.readWhen[C]('on, 'holds, 'st) }

  /** From the moment on, no `val` of the object's class is being written, marked or written. */
  inline def valsAreSettled(w: Moment)(using st: Stating): Term[Boolean] = ${ ValMacros.settled[C]('on, 'w, 'st) }

  /** No `val` of the object's class has a data race. */
  inline def hasNoRaceOnItsVals(using st: Stating): Term[Boolean] = ${ ValMacros.unraced[C]('on, 'st) }

object ValMacros:
  import FieldMacros.{taking, vals}

  def assigned[C: Type](on: Expr[Obj[C]], st: Expr[Stating])(using Quotes): Expr[Term[Boolean]] =
    '{ Vals.assigned(${ Expr(vals[C]) }, $on.asValue)(using $st) }

  def readItself[C: Type](on: Expr[Obj[C]], also: Expr[(Term[Value], Moment) => Term[Boolean]], st: Expr[Stating])(
      using Quotes): Expr[Term[Boolean]] =
    '{ Vals.readItself(${ Expr(vals[C]) }, ${ Expr(taking[C]) }, $on.asValue, $also)(using $st) }

  def readWhen[C: Type](on: Expr[Obj[C]], holds: Expr[Moment => Term[Boolean]], st: Expr[Stating])(using Quotes)
      : Expr[Term[Boolean]] =
    '{ Vals.readWhen(${ Expr(vals[C]) }, $on.asValue, $holds)(using $st) }

  def settled[C: Type](on: Expr[Obj[C]], w: Expr[Moment], st: Expr[Stating])(using Quotes): Expr[Term[Boolean]] =
    '{ Vals.settled(${ Expr(vals[C]) }, $on.asValue, $w)(using $st) }

  def unraced[C: Type](on: Expr[Obj[C]], st: Expr[Stating])(using Quotes): Expr[Term[Boolean]] =
    '{ Vals.unracedAll(${ Expr(vals[C]) }, $on.asValue)(using $st) }

/** What the macros make: statements of each field among the names. */
object Vals:
  private def among(names: List[String], field: Term[String]): Term[Boolean] = names.map(field === _).reduce(_ || _)

  def assigned(names: List[String], on: Term[Value])(using Stating): Term[Boolean] =
    forall((field: Term[String], by: Term[Value], inside: Term[Option[BigInt]], w: Term[BigInt]) =>
      (among(names, field) && assigns(on, field, by, inside, w)) implies
        exists((m: Term[BigInt], cls: Term[String], holding: Term[List[Held]]) =>
          m < w && history(m) === make[Event.Make](by, inside, on, cls, holding)))

  def readItself(names: List[String], methods: List[(String, Int)], on: Term[Value],
      also: (Term[Value], Moment) => Term[Boolean])(using Stating): Term[Boolean] =
    forall((field: Term[String], by: Term[Value], inside: Term[Option[BigInt]], w: Term[BigInt]) =>
      (among(names, field) && readsField(on, field, by, inside, w)) implies
        exists((i: Term[BigInt]) =>
          inside === some(i) && i < w && (Fields.calledBy(methods, on, by, i) || also(by, i))))

  def readWhen(names: List[String], on: Term[Value], holds: Moment => Term[Boolean])(using Stating): Term[Boolean] =
    forall((field: Term[String], by: Term[Value], inside: Term[Option[BigInt]], w: Term[BigInt]) =>
      (among(names, field) && readsField(on, field, by, inside, w)) implies holds(w))

  def settled(names: List[String], on: Term[Value], w: Moment)(using Stating): Term[Boolean] =
    forall((field: Term[String], by: Term[Value], inside: Term[Option[BigInt]], later: Term[BigInt]) =>
      (among(names, field) && w <= later) implies
        (!writing(on, field, by, later) && !assigns(on, field, by, inside, later)))

  def unracedAll(names: List[String], on: Term[Value])(using Stating): Term[Boolean] =
    forall((field: Term[String]) => among(names, field) implies unraced(on, field))

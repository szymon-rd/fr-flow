package frflow.code

import frflow.{Call as _, *}
import frflow.executions.{Call, World}
import frflow.values.{Obj, Value}

// What an object holds. A field is named as the tree read from its class's TASTy names it; what it holds is a
// value of the code. A statement may name a field code outside the class may not.

/** What a field that is assigned once holds, of an object. */
val heldIn = Declaration[(String, Value) => Value]("what a field that is assigned once holds, of an object")

/** What a field that is assigned again holds, of an object at a moment. */
val heldAt = Declaration[(String, Value, BigInt) => Value]("what a field holds, of an object at a moment")

extension [C](on: Obj[C])
  /** The field of the object named `name`: of a `val`, what it holds (`h.field("threads")`); of a `var`, what it
    * holds at each moment (`h.field("count").at(w)`).
    */
  transparent inline def field(inline name: String)(using st: Stating): Any =
    ${ FieldMacros.field[C]('on, 'name, 'st) }

extension [C](on: Obj[C])
  /** The object has been made, of its class, before the moment: by the code read. */
  inline def isMade(w: World)(using st: Stating): Term[Boolean] = ${ FieldMacros.made[C]('on, 'w, 'st) }

  /** Every read of the field finds what it holds (`field`): what Scala says of a `val`. */
  inline def readsAsHeld(inline name: String)(using st: Stating): Term[Boolean] =
    ${ FieldMacros.reads[C]('on, 'name, 'st) }

  /** Every read of a `val` of the object's class finds what it holds: each field the class assigns once. */
  inline def readsItsValsAsHeld(using st: Stating): Term[Boolean] = ${ FieldMacros.readsVals[C]('on, 'st) }

  /** A method of the object's class is called on it only once it has been made. */
  inline def isMadeWhenCalled(using st: Stating): Term[Boolean] = ${ FieldMacros.madeWhenCalled[C]('on, 'st) }

  /** A completed call of the constructor of the object's class has returned the object by the moment. */
  inline def isConstructed(w: World)(using st: Stating): Term[Boolean] =
    ${ FieldMacros.constructed[C]('on, 'w, 'st) }

  /** A method of the object's class is called on it only once a call of the class's constructor has returned it. */
  inline def isConstructedWhenCalled(using st: Stating): Term[Boolean] =
    ${ FieldMacros.constructedWhenCalled[C]('on, 'st) }

  /** Each `val` of the object's class holds what it is given when the object is made: every write of one writes
    * what it holds (`field`).
    */
  inline def holdsWhatItsValsAreGiven(using st: Stating): Term[Boolean] = ${ FieldMacros.givenVals[C]('on, 'st) }

  /** A call of a method of the object's class on the object is made at the moment by `by`. */
  inline def isCalledBy(by: Term[Value], w: World)(using st: Stating): Term[Boolean] =
    ${ FieldMacros.calledBy[C]('on, 'by, 'w, 'st) }

  /** What the object keeps to itself: every call on `kept` is made itself by a call of a method of the object's
    * class on the object, or by a call `also` says (of a function the object handed out).
    */
  inline def keepsToItself(kept: Term[Value])(also: (Term[Value], World) => Term[Boolean])(using st: Stating)
      : Term[Boolean] = ${ FieldMacros.keeps[C]('on, 'kept, 'also, 'st) }

  /** A call of the method of the object's class named `name`, given `arguments`: a statement may name a method
    * code outside the class may not (`h.method[Unit]("assertNotShuttingDown")`).
    */
  inline def method[A](inline name: String, arguments: Term[Value]*): Call[A] =
    ${ FieldMacros.method[C, A]('on, 'name, 'arguments) }

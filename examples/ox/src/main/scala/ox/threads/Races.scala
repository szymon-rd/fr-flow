package ox.threads

import frflow.*
import frflow.code.*
import frflow.executions.*
import frflow.values.*
import ox.internal.ThreadHerd

// That no field of a herd has a data race. A herd's fields are its four vals. A plain write is two events, a
// mark and the write, and a field is being written from the one to the other; a race is a read, a mark or a write
// of the field by another thread meanwhile (JLS 17.4.5: two accesses, one of them a write, that nothing orders).
// It is said of every execution of the code, in whatever order the threads take their turns.

// Assumed, of the JVM. A val is a final field: the JVM lets it be assigned only in a constructor of its class
// (JVMS 6.5, putfield), and a constructor runs on an object once, where the object is made (JVMS 4.10.2.4). Where
// the code makes a herd, the constructor's events are the making call's own.
val aHerdsValsAreAssignedWhereItIsMade = Node.assumption(
  "A val of a herd is marked and written only by the thread that makes the herd, inside the call that makes it.")(
  forall((h: Obj[ThreadHerd]) => h.assignsItsValsWhereMade)).about(About.jdk)

// Assumed, of the JVM and of the code. The fields are private: only code of the herd's class is let read them
// (JVMS 5.4.4). That code is the herd's methods, which read the fields of the herd they are called on, and the
// functions written in them, of which only the one startThread hands the factory reads a field.
val aHerdsValsAreReadByItsCode = Node.assumption(
  "A val of a herd is read only by a method of the herd called on it, or by a function startThread handed its " +
    "factory, themselves.")(
  forall((h: Obj[ThreadHerd]) => h.readsItsValsItself((by, i) => aForkFunctionRuns(h, by, i)))).about(About.readers)

val aReadyHerdsValsAreWritten = Node.claim(
  "Once a herd is ready, none of its vals is being written, and none is marked or written again.")(
  forall((h: Obj[ThreadHerd], w: Term[BigInt]) => ready(h, w) implies h.valsAreSettled(w)))

val aHerdsValsAreReadOnceItIsReady = Node.claim("A val of a herd is read only once the herd is ready.")(
  forall((h: Obj[ThreadHerd]) => h.readsItsValsOnlyWhen(w => ready(h, w))))

val noRaceOnAHerdsVals = Node.claim(
  "No thread reads, marks or writes a val of a herd while another thread is writing it.")(
  forall((h: Obj[ThreadHerd]) => h.hasNoRaceOnItsVals))

// The two variables closing makes are the other memory the herd's code writes plainly. That only closing's caller
// touches them is assumed (`closingKeepsItsVariableToItself`): with it they have no race.
val noRaceOnClosingsVariables = Node.claim(
  "No thread reads, marks or writes a variable that a call of closing itself made while another thread is " +
    "writing it.")(
  forall((h: Obj[ThreadHerd], c: Obj[Thread], from: Term[BigInt], made: Term[Value], field: Term[String]) =>
    (closing(h).by(c).called(from) && itselfCreates(made, c.asValue, from)) implies unraced(made, field)))

/** That what the herd's code writes plainly has no data race, and what it is from. */
val withoutRaces: List[FrModel.Part] = List(
  noRaceOnAHerdsVals, noRaceOnClosingsVariables,
  aReadyHerdsValsAreWritten.refines(noRaceOnAHerdsVals),
  aHerdsValsAreReadOnceItIsReady.refines(noRaceOnAHerdsVals),
  aHerdsValsAreAssignedWhereItIsMade.refines(noRaceOnAHerdsVals, aReadyHerdsValsAreWritten),
  aHerdsValsAreReadByItsCode.refines(aHerdsValsAreReadOnceItIsReady))

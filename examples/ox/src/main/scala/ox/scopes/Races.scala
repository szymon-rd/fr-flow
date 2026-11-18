package ox.scopes

import frflow.*
import frflow.code.*
import frflow.values.*
import ox.threads.{About, Scope}

// That no field of a scope has a data race: as of a herd (`ox.threads`, Races). A scope's fields are the six vals
// of its class; the variable its trait keeps for a lazy val is entered by Scala's own protocol, and is not one.

// Assumed, of the JVM: a val is a final field, assigned only in a constructor of its class, which runs on an
// object once, where it is made (JVMS 6.5, putfield; 4.10.2.4).
val aScopesValsAreAssignedWhereItIsMade = Node.assumption(
  "A val of a scope is marked and written only by the thread that makes the scope, inside the call that makes " +
    "it.")(
  forall((s: Obj[Scope]) => s.assignsItsValsWhereMade)).about(About.jdk)

// Assumed, of the code and of who is given a scope. The constructor of a scope hands the scope to nothing: what
// it runs gives each val what the call was given. So a scope is in other hands only once its constructor has
// returned it, which is what the JVM asks of a final field for its readers to see it assigned (JLS 17.5).
val aScopesValsAreReadOnceItIsConstructed = Node.assumption(
  "A val of a scope is read only once a call of its class's constructor has returned the scope.")(
  forall((s: Obj[Scope]) => s.readsItsValsOnlyWhen(w => s.isConstructed(w)))).about(About.readers)

val aConstructedScopesValsAreWritten = Node.claim(
  "Once a call of its class's constructor has returned a scope, none of its vals is being written, and none is " +
    "marked or written again.")(
  forall((s: Obj[Scope], w: Term[BigInt]) => s.isConstructed(w) implies s.valsAreSettled(w)))
  .from(aScopesValsAreAssignedWhereItIsMade)

val noRaceOnAScopesVals = Node.claim(
  "No thread reads, marks or writes a val of a scope while another thread is writing it.")(
  forall((s: Obj[Scope]) => s.hasNoRaceOnItsVals))
  .from(aConstructedScopesValsAreWritten, aScopesValsAreReadOnceItIsConstructed, aScopesValsAreAssignedWhereItIsMade)

/** That a scope's fields have no data race, with the statements it is from. */
val scopesWithoutRaces: List[FrModel.Part] = List(
  noRaceOnAScopesVals, aConstructedScopesValsAreWritten, aScopesValsAreReadOnceItIsConstructed,
  aScopesValsAreAssignedWhereItIsMade)

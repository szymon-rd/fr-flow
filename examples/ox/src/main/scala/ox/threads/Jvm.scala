package ox.threads

import frflow.{Call as _, *}
import frflow.code.*
import frflow.code.InCode.given
import frflow.executions.*
import frflow.values.*
import java.util.concurrent.ConcurrentHashMap
import java.util.concurrent.atomic.AtomicBoolean

// What is assumed of the JDK's methods that Ox calls. A call takes time, and others act during it. Where the JDK
// says a call is atomic, what is assumed is that it takes effect at one moment during it.

/** What is in a concurrent set at a moment. It is no member of the JDK's: it is what the assumptions speak of. */
val elements = Declaration[(Ref[ConcurrentSet], BigInt) => Set[Value]]("what is in the set at a moment")

/** What an atomic boolean holds at a moment. */
val flag = Declaration[(Ref[AtomicBoolean], BigInt) => Boolean]("what the atomic boolean holds at a moment")

/** The set is one made by `ConcurrentHashMap.newKeySet`, and nothing but `add`, `remove`, `contains`, `isEmpty`
  * and `forEach` is ever called on it. Its map is then its own, and no call gives out the map or an iterator over
  * the set: what is in it changes only by what is added to it and removed from it.
  */
val plainSet = stated { (s: Obj[ConcurrentSet]) =>
  exists((from: Moment, to: Moment) =>
    ConcurrentHashMap.newKeySet[AnyRef]().completed(from, Returned(s), to)) &&
    forall((method: Term[String], w: Moment) =>
      calledOn(s.asValue, method, w) implies
        (method === methodOf[ConcurrentSet](_.add(???)) || method === methodOf[ConcurrentSet](_.remove(???)) ||
          method === methodOf[ConcurrentSet](_.contains(???)) || method === methodOf[ConcurrentSet](_.isEmpty()) ||
          method === methodOf[ConcurrentSet](_.forEach(???)))) }

/** Nothing but `get` and `set` is ever called on the atomic boolean. */
val onlyReadAndSet = stated { (s: Obj[AtomicBoolean]) =>
  forall((method: Term[String], w: Moment) =>
    calledOn(s.asValue, method, w) implies
      (method === methodOf[AtomicBoolean](_.get()) || method === methodOf[AtomicBoolean](_.set(???)))) }

/** An element is being added to the set at some moment from `from` to `to`: a call that adds is pending at
  * `from`, or is made before `to`.
  */
val addedDuring = stated { (s: Obj[ConcurrentSet], from: Moment, to: Moment) =>
  exists((x: Obj[AnyRef]) => s.add(x).pendingAt(from) || s.add(x).calledWithin(from, to)) }

val addingIsAtomic = Node.assumption(
  "Adding to a concurrent set is atomic: at one moment during the call, the element is put in the set.")(
  forall((s: Obj[ConcurrentSet], x: Obj[AnyRef]) =>
    s.add(x).atomic((before, after) => forall((y: Term[Value]) =>
      elements(s, after).contains(y) === (y === x.asValue || elements(s, before).contains(y)))))).about(About.jdk)

val anElementLeavesOnlyWhenRemoved = Node.assumption(
  "An element leaves a plain concurrent set only at a moment during a call that removes it.")(
  forall((s: Obj[ConcurrentSet], x: Obj[AnyRef], w: Moment) =>
    (plainSet(s) && elements(s, w).contains(x.asValue) && !elements(s, w + 1).contains(x.asValue)) implies
      s.remove(x).inProgress(w))).about(About.jdk)

val getGivesTheFlag = Node.assumption("Reading an atomic boolean gives what it holds at a moment during the read.")(
  forall((s: Obj[AtomicBoolean], b: Term[Boolean]) =>
    s.get().everyCall((from, a, to) =>
      (a === Returned(b)) implies exists((m: Moment) => from <= m && m < to && (flag(s, m) === b)))))
    .about(About.jdk)

val settingIsAtomic = Node.assumption(
  "Setting an atomic boolean is atomic: at one moment during the call, it comes to hold what is set.")(
  forall((s: Obj[AtomicBoolean], b: Term[Boolean]) => s.set(b).atomic((_, after) => flag(s, after) === b)))
    .about(About.jdk)

val aFlagBecomesOnlyWhatIsSet = Node.assumption(
  "What an atomic boolean that is only read and set holds becomes a value only at a moment during a call that " +
    "sets it to that value.")(
  forall((s: Obj[AtomicBoolean], v: Term[Boolean], w: Moment) =>
    (onlyReadAndSet(s) && (flag(s, w) =!= v) && (flag(s, w + 1) === v)) implies s.set(v).inProgress(w)))
    .about(About.jdk)

val currentThreadIsTheCaller = Node.assumption("`Thread.currentThread()` gives the thread that calls it.")(
  forall((c: Obj[Thread]) => Thread.currentThread().by(c).everyCall((_, a, _) => a === Returned(c)))).about(About.jdk)

val setReturns = Node.assumption("Setting an atomic boolean does not throw.")(
  forall((s: Obj[AtomicBoolean], b: Term[Boolean]) => s.set(b).everyCall((_, a, _) => a === Returned(()))))
    .about(About.jdk)

val isEmptyReturns = Node.assumption("Asking a concurrent set whether it is empty does not throw.")(
  forall((s: Obj[ConcurrentSet]) =>
    s.isEmpty().everyCall((_, a, _) => (a === Returned(True)) || (a === Returned(False))))).about(About.jdk)

// `isEmpty` is no snapshot: it sums counters read one after another (`ConcurrentHashMap.sumCount`), and the JDK
// says its answer is for use only where no other thread changes the set meanwhile. What is assumed is what that
// sum gives when nothing is added during the call: every element is counted before it, and elements only leave.
val isEmptyFindsItEmptyUnlessAdded = Node.assumption(
  "A concurrent set that answers that it is empty, with nothing added to it during the call, is empty at a " +
    "moment during the call.")(
  forall((s: Obj[ConcurrentSet]) =>
    s.isEmpty().everyCall((from, a, to) =>
      ((a === Returned(True)) && !addedDuring(s, from, to)) implies exists((m: Moment) =>
        from <= m && m <= to && forall((y: Term[Value]) => !elements(s, m).contains(y)))))).about(About.jdk)

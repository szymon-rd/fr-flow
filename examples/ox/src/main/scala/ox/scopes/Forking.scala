package ox.scopes

import frflow.{Call as _, *}
import frflow.code.*
import frflow.executions.*
import frflow.values.*
import ox.threads.*

// A fork is started by calling `startThread` on the herd of its scope: so starting a fork in a scope whose herd
// is closed does not return. Of `forkUnsupervised` and of `forkCancellable`, read from Ox's code.

/** Starting a fork of the code in the scope, unsupervised: `forkUnsupervised(code)(using s)`. */
def forkingUnsupervised(code: Term[Value], s: Obj[Scope]): Call[Any] =
  Call.of[Any](methodCalled(ox.forkUnsupervised[Any](???)(using ???)), code, s.asValue)

val forkUnsupervisedStartsAThread = Node.claim(
  "A call of forkUnsupervised returns only after a call of startThread on the herd of its scope, that it made " +
    "itself, has returned.")(
  forall((code: Term[Value], s: Obj[Scope], c: Obj[Thread]) =>
    forall((from: Term[BigInt], fork: Term[Value], to: Term[BigInt]) =>
      forkingUnsupervised(code, s).by(c).completed(from, make[Response.Returned](fork), to) implies
        exists((run: Obj[Code], a: Term[BigInt], b: Term[BigInt]) =>
          from < a && b <= to && starting(herdOf(s), run).by(c).calledInside(from, a) &&
            starting(herdOf(s), run).by(c).completed(a, Returned(()), b)))))

val forkUnsupervisedIsRefusedOnceClosed = Node.claim(
  "After closing a herd has completed, a call of forkUnsupervised in a scope that holds the herd does not " +
    "return.")(
  forall((code: Term[Value], s: Obj[Scope], c: Obj[Thread]) =>
    forall((m: Term[BigInt], fork: Term[Value], w: Term[BigInt]) =>
      (closed(herdOf(s), m) && forkingUnsupervised(code, s).by(c).called(m)) implies
        !forkingUnsupervised(code, s).by(c).completed(m, make[Response.Returned](fork), w))))

val forkUnsupervisedIsRefusedOnceUnsupervisedEnds = Node.claim(
  "After a call of unsupervised has completed, a call of forkUnsupervised in the scope it made does not return.")(
  forall((c: Obj[Thread], s: Obj[Scope], from: Term[BigInt], to: Term[BigInt]) =>
    forall((code: Term[Value], d: Obj[Thread], m: Term[BigInt], fork: Term[Value], w: Term[BigInt]) =>
      (unsupervisedMade(c, s, from, to) && to <= m && forkingUnsupervised(code, s).by(d).called(m)) implies
        !forkingUnsupervised(code, s).by(d).completed(m, make[Response.Returned](fork), w))))

val forkUnsupervisedIsRefusedOnceSupervisedEnds = Node.claim(
  "After a call of supervised has completed, a call of forkUnsupervised in the scope it made does not return.")(
  forall((c: Obj[Thread], s: Obj[Scope], from: Term[BigInt], to: Term[BigInt]) =>
    forall((code: Term[Value], d: Obj[Thread], m: Term[BigInt], fork: Term[Value], w: Term[BigInt]) =>
      (supervisedMade(c, s, from, to) && to <= m && forkingUnsupervised(code, s).by(d).called(m)) implies
        !forkingUnsupervised(code, s).by(d).completed(m, make[Response.Returned](fork), w))))

/** Starting a fork of the code in the scope, that can be cancelled: `forkCancellable(code)(using s)`. */
def forkingCancellable(code: Term[Value], s: Obj[Scope]): Call[Any] =
  Call.of[Any](methodCalled(ox.forkCancellable[Any](???)(using ???)), code, s.asValue)

val forkCancellableStartsAThread = Node.claim(
  "A call of forkCancellable returns only after a call of startThread on the herd of its scope, that it made " +
    "itself, has returned.")(
  forall((code: Term[Value], s: Obj[Scope], c: Obj[Thread]) =>
    forall((from: Term[BigInt], fork: Term[Value], to: Term[BigInt]) =>
      forkingCancellable(code, s).by(c).completed(from, make[Response.Returned](fork), to) implies
        exists((run: Obj[Code], a: Term[BigInt], b: Term[BigInt]) =>
          from < a && b <= to && starting(herdOf(s), run).by(c).calledInside(from, a) &&
            starting(herdOf(s), run).by(c).completed(a, Returned(()), b)))))

val forkCancellableIsRefusedOnceClosed = Node.claim(
  "After closing a herd has completed, a call of forkCancellable in a scope that holds the herd does not " +
    "return.")(
  forall((code: Term[Value], s: Obj[Scope], c: Obj[Thread]) =>
    forall((m: Term[BigInt], fork: Term[Value], w: Term[BigInt]) =>
      (closed(herdOf(s), m) && forkingCancellable(code, s).by(c).called(m)) implies
        !forkingCancellable(code, s).by(c).completed(m, make[Response.Returned](fork), w))))

val forkCancellableIsRefusedOnceUnsupervisedEnds = Node.claim(
  "After a call of unsupervised has completed, a call of forkCancellable in the scope it made does not return.")(
  forall((c: Obj[Thread], s: Obj[Scope], from: Term[BigInt], to: Term[BigInt]) =>
    forall((code: Term[Value], d: Obj[Thread], m: Term[BigInt], fork: Term[Value], w: Term[BigInt]) =>
      (unsupervisedMade(c, s, from, to) && to <= m && forkingCancellable(code, s).by(d).called(m)) implies
        !forkingCancellable(code, s).by(d).completed(m, make[Response.Returned](fork), w))))

val forkCancellableIsRefusedOnceSupervisedEnds = Node.claim(
  "After a call of supervised has completed, a call of forkCancellable in the scope it made does not return.")(
  forall((c: Obj[Thread], s: Obj[Scope], from: Term[BigInt], to: Term[BigInt]) =>
    forall((code: Term[Value], d: Obj[Thread], m: Term[BigInt], fork: Term[Value], w: Term[BigInt]) =>
      (supervisedMade(c, s, from, to) && to <= m && forkingCancellable(code, s).by(d).called(m)) implies
        !forkingCancellable(code, s).by(d).completed(m, make[Response.Returned](fork), w))))

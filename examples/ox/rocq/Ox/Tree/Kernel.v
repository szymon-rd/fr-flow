(** The concurrency kernel of Ox 1.1.0: what its scopes, forks, fork locals, resources, `par`, `race`, `timeout`
    and the rest of its control operators reach, computed from Ox's trees (`All.v`).

    `api` names what declares the operators a program calls. `kernel` is every definition of Ox those may run
    (`FrFlow.Scala.Program`, `reaches`: at least what runs). `kernel_surface` is what the kernel takes from
    outside Ox: the definitions of the JDK and of Scala's library whose behaviour a proof about Ox's concurrency
    rests on. Rocq checks the list against what it computes from the trees (`kernel_surface_is`), so it is exact:
    116 definitions the operators declare reach 320 of the 2460 that Ox defines, and take 184 from outside,
    68 of them the JDK's.

    Kept by hand: when Ox's trees change, `kernel_surface_is` fails, and the list is taken anew from what Rocq
    computes (`Eval vm_compute in reaches_outside "ox" files kernel`). *)

From Stdlib Require Import String List.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Program Ox.Tree.All.
Import ListNotations.
Open Scope string_scope.

Definition api : list string :=
  ["ox.supervised$package$"; "ox.unsupervised$package$"; "ox.fork$package$"; "ox.Fork"; "ox.UnsupervisedFork";
   "ox.CancellableFork"; "ox.ForkLocal"; "ox.ForkLocal$"; "ox.local$package$"; "ox.resource$package$";
   "ox.par$package$"; "ox.race$package$"; "ox.util$package$"; "ox.control$package$"].

Definition reached : list sym * list sym := Eval vm_compute in reaches "ox" files (declared_by files api).

(** Every definition of Ox the operators may run. *)
Definition kernel : list sym := fst reached.

(** The search for them ended: nothing was left to look at. *)
Lemma kernel_whole : snd reached = [].
Proof. reflexivity. Qed.

Lemma kernel_size :
  (length (declared_by files api), length kernel, length (over_list defines files)) = (116, 320, 2460).
Proof. vm_compute. reflexivity. Qed.

Definition kernel_surface : list sym :=
  [Member "<special-ops>" "throw" "java.lang.Throwable:scala.Nothing";
   Member "java.lang" "System" "";
   Member "java.lang" "Thread" "";
   Member "java.lang.AutoCloseable" "close" ":scala.Unit";
   Member "java.lang.Class" "isInstance" "java.lang.Object:scala.Boolean";
   Member "java.lang.IllegalStateException" "<init>" ":java.lang.IllegalStateException";
   Member "java.lang.IllegalStateException" "<init>" "java.lang.String:java.lang.IllegalStateException";
   Member "java.lang.IndexOutOfBoundsException" "<init>" "scala.Int:java.lang.IndexOutOfBoundsException";
   Member "java.lang.InterruptedException" "<init>" ":java.lang.InterruptedException";
   Member "java.lang.InterruptedException" "<init>" "java.lang.String:java.lang.InterruptedException";
   Member "java.lang.Iterable" "forEach" "java.util.function.Consumer:scala.Unit";
   Member "java.lang.Object" "<init>" ":java.lang.Object";
   Member "java.lang.Object" "eq" "java.lang.Object:scala.Boolean";
   Member "java.lang.RuntimeException" "<init>" "java.lang.String:java.lang.RuntimeException";
   Member "java.lang.String" "+" "java.lang.Object:java.lang.String";
   Member "java.lang.String" "hashCode" ":scala.Int";
   Member "java.lang.System$" "nanoTime" ":scala.Long";
   Member "java.lang.Thread" "getName" ":java.lang.String";
   Member "java.lang.Thread" "interrupt" ":scala.Unit";
   Member "java.lang.Thread" "join" ":scala.Unit";
   Member "java.lang.Thread" "start" ":scala.Unit";
   Member "java.lang.Thread$" "currentThread" ":java.lang.Thread";
   Member "java.lang.Thread$" "interrupted" ":scala.Boolean";
   Member "java.lang.Thread$" "ofVirtual" ":java.lang.Thread$.Builder$.OfVirtual";
   Member "java.lang.Thread$" "sleep" "scala.Long:scala.Unit";
   Member "java.lang.Thread$" "yield" ":scala.Unit";
   Member "java.lang.Thread$.Builder" "factory" ":java.util.concurrent.ThreadFactory";
   Member "java.lang.ThreadLocal" "<init>" "1:java.lang.ThreadLocal";
   Member "java.lang.ThreadLocal" "get" ":java.lang.Object";
   Member "java.lang.ThreadLocal" "set" "java.lang.Object:scala.Unit";
   Member "java.lang.Throwable" "<init>" "java.lang.String:java.lang.Throwable";
   Member "java.lang.Throwable" "addSuppressed" "java.lang.Throwable:scala.Unit";
   Member "java.lang.Throwable" "getCause" ":java.lang.Throwable";
   Member "java.util.NoSuchElementException" "<init>" ":java.util.NoSuchElementException";
   Member "java.util.NoSuchElementException" "<init>" "java.lang.String:java.util.NoSuchElementException";
   Member "java.util.Set" "add" "java.lang.Object:scala.Boolean";
   Member "java.util.concurrent" "ConcurrentHashMap" "";
   Member "java.util.concurrent.ArrayBlockingQueue" "<init>" "1,scala.Int:java.util.concurrent.ArrayBlockingQueue";
   Member "java.util.concurrent.ArrayBlockingQueue" "put" "java.lang.Object:scala.Unit";
   Member "java.util.concurrent.ArrayBlockingQueue" "take" ":java.lang.Object";
   Member "java.util.concurrent.CompletableFuture" "<init>" "1:java.util.concurrent.CompletableFuture";
   Member "java.util.concurrent.CompletableFuture" "complete" "java.lang.Object:scala.Boolean";
   Member "java.util.concurrent.CompletableFuture" "completeExceptionally" "java.lang.Throwable:scala.Boolean";
   Member "java.util.concurrent.CompletableFuture" "exceptionNow" ":java.lang.Throwable";
   Member "java.util.concurrent.CompletableFuture" "get" ":java.lang.Object";
   Member "java.util.concurrent.CompletableFuture" "isCompletedExceptionally" ":scala.Boolean";
   Member "java.util.concurrent.ConcurrentHashMap$" "newKeySet" "1:java.util.concurrent.ConcurrentHashMap$.KeySetView";
   Member "java.util.concurrent.ConcurrentHashMap$.CollectionView" "isEmpty" ":scala.Boolean";
   Member "java.util.concurrent.ConcurrentHashMap$.KeySetView" "add" "java.lang.Object:scala.Boolean";
   Member "java.util.concurrent.ConcurrentHashMap$.KeySetView" "contains" "java.lang.Object:scala.Boolean";
   Member "java.util.concurrent.ConcurrentHashMap$.KeySetView" "forEach" "java.util.function.Consumer:scala.Unit";
   Member "java.util.concurrent.ConcurrentHashMap$.KeySetView" "remove" "java.lang.Object:scala.Boolean";
   Member "java.util.concurrent.Semaphore" "<init>" "scala.Int:java.util.concurrent.Semaphore";
   Member "java.util.concurrent.Semaphore" "acquire" ":scala.Unit";
   Member "java.util.concurrent.Semaphore" "release" ":scala.Unit";
   Member "java.util.concurrent.ThreadFactory" "newThread" "java.lang.Runnable:java.lang.Thread";
   Member "java.util.concurrent.TimeoutException" "<init>" "java.lang.String:java.util.concurrent.TimeoutException";
   Member "java.util.concurrent.atomic.AtomicBoolean" "<init>" "scala.Boolean:java.util.concurrent.atomic.AtomicBoolean";
   Member "java.util.concurrent.atomic.AtomicBoolean" "get" ":scala.Boolean";
   Member "java.util.concurrent.atomic.AtomicBoolean" "getAndSet" "scala.Boolean:scala.Boolean";
   Member "java.util.concurrent.atomic.AtomicBoolean" "set" "scala.Boolean:scala.Unit";
   Member "java.util.concurrent.atomic.AtomicInteger" "<init>" "scala.Int:java.util.concurrent.atomic.AtomicInteger";
   Member "java.util.concurrent.atomic.AtomicInteger" "decrementAndGet" ":scala.Int";
   Member "java.util.concurrent.atomic.AtomicInteger" "incrementAndGet" ":scala.Int";
   Member "java.util.concurrent.atomic.AtomicReference" "<init>" "1,java.lang.Object:java.util.concurrent.atomic.AtomicReference";
   Member "java.util.concurrent.atomic.AtomicReference" "getAndSet" "java.lang.Object:java.lang.Object";
   Member "java.util.concurrent.atomic.AtomicReference" "updateAndGet" "java.util.function.UnaryOperator:java.lang.Object";
   Member "java.util.concurrent.locks" "LockSupport" "";
   Member "java.util.concurrent.locks.LockSupport$" "park" ":scala.Unit";
   Member "scala" "Array" "";
   Member "scala" "None" "";
   Member "scala" "Option" "";
   Member "scala" "Some" "";
   Member "scala" "StringContext" "";
   Member "scala" "Tuple2" "";
   Member "scala" "Tuple3" "";
   Member "scala" "Tuple4" "";
   Member "scala.Any" "!=" "java.lang.Object:scala.Boolean";
   Member "scala.Any" "$asInstanceOf$" "1:java.lang.Object";
   Member "scala.Any" "==" "java.lang.Object:scala.Boolean";
   Member "scala.Any" "asInstanceOf" "1:java.lang.Object";
   Member "scala.Any" "isInstanceOf" "1:scala.Boolean";
   Member "scala.Any" "toString" ":java.lang.String";
   Member "scala.Array" "apply" "scala.Int:java.lang.Object";
   Member "scala.Array$" "apply" "1,scala.collection.immutable.Seq,scala.reflect.ClassTag:java.lang.Object";
   Member "scala.Boolean" "&&" "scala.Boolean:scala.Boolean";
   Member "scala.Boolean" "unary_!" ":";
   Member "scala.Boolean" "||" "scala.Boolean:scala.Boolean";
   Member "scala.ContextFunction1" "apply" "java.lang.Object:java.lang.Object";
   Member "scala.Equals" "canEqual" "java.lang.Object:scala.Boolean";
   Member "scala.Function0" "apply" ":java.lang.Object";
   Member "scala.Function1" "apply" "java.lang.Object:java.lang.Object";
   Member "scala.Int" "-" "scala.Int:scala.Int";
   Member "scala.Int" "==" "scala.Int:scala.Boolean";
   Member "scala.Long" "-" "scala.Long:scala.Long";
   Member "scala.Option" "getOrElse" "1,scala.Function0:java.lang.Object";
   Member "scala.Option" "isDefined" ":";
   Member "scala.Option$" "apply" "1,java.lang.Object:scala.Option";
   Member "scala.Predef$" "Map" "";
   Member "scala.Predef$" "Set" "";
   Member "scala.Predef$" "classOf" "1:java.lang.Class";
   Member "scala.Predef$" "println" "java.lang.Object:scala.Unit";
   Member "scala.Product" "productElement" "scala.Int:java.lang.Object";
   Member "scala.Some$" "apply" "1,java.lang.Object:scala.Some";
   Member "scala.Some$" "unapply" "1,scala.Some:scala.Option";
   Member "scala.StringContext" "s" "scala.collection.immutable.Seq:java.lang.String";
   Member "scala.StringContext$" "apply" "scala.collection.immutable.Seq:scala.StringContext";
   Member "scala.Tuple2$" "apply" "2,java.lang.Object,java.lang.Object:scala.Tuple2";
   Member "scala.Tuple2$" "unapply" "2,scala.Tuple2:scala.Option";
   Member "scala.Tuple3$" "apply" "3,java.lang.Object,java.lang.Object,java.lang.Object:scala.Tuple3";
   Member "scala.Tuple4$" "apply" "4,java.lang.Object,java.lang.Object,java.lang.Object,java.lang.Object:scala.Tuple4";
   Member "scala.collection.IndexedSeqOps" "headOption" ":";
   Member "scala.collection.IterableFactory" "apply" "1,scala.collection.immutable.Seq:java.lang.Object";
   Member "scala.collection.IterableOnceOps" "exists" "scala.Function1:scala.Boolean";
   Member "scala.collection.IterableOnceOps" "foldLeft" "1,java.lang.Object,scala.Function2:java.lang.Object";
   Member "scala.collection.IterableOnceOps" "foreach" "1,scala.Function1:scala.Unit";
   Member "scala.collection.IterableOnceOps" "toVector" ":";
   Member "scala.collection.IterableOps" "head" ":";
   Member "scala.collection.IterableOps" "map" "1,scala.Function1:java.lang.Object";
   Member "scala.collection.IterableOps" "tail" ":";
   Member "scala.collection.MapOps" "get" "java.lang.Object:scala.Option";
   Member "scala.collection.SeqOps" ":+" "1,java.lang.Object:java.lang.Object";
   Member "scala.collection.SeqOps" "apply" "scala.Int:java.lang.Object";
   Member "scala.collection.SeqOps" "size" ":";
   Member "scala.collection.SetOps" "contains" "java.lang.Object:scala.Boolean";
   Member "scala.collection.immutable.List" "::" "1,java.lang.Object:scala.collection.immutable.List";
   Member "scala.collection.immutable.List" "flatMap" "1,scala.Function1:scala.collection.immutable.List";
   Member "scala.collection.immutable.List" "foreach" "1,scala.Function1:scala.Unit";
   Member "scala.collection.immutable.List" "isEmpty" ":";
   Member "scala.collection.immutable.Map$" "empty" "2:scala.collection.immutable.Map";
   Member "scala.collection.immutable.MapOps" "updated" "1,java.lang.Object,java.lang.Object:scala.collection.immutable.MapOps";
   Member "scala.collection.immutable.Set$" "empty" "1:scala.collection.immutable.Set";
   Member "scala.collection.immutable.SetOps" "+" "java.lang.Object:scala.collection.immutable.SetOps";
   Member "scala.collection.immutable.Vector" "foreach" "1,scala.Function1:scala.Unit";
   Member "scala.collection.immutable.Vector" "tail" ":";
   Member "scala.collection.immutable.Vector$" "empty" "1:scala.collection.immutable.Vector";
   Member "scala.compiletime.package$package$" "uninitialized" ":";
   Member "scala.concurrent" "Await" "";
   Member "scala.concurrent.Await$" "result" "1,scala.concurrent.Awaitable,scala.concurrent.duration.Duration:java.lang.Object";
   Member "scala.concurrent.duration" "Duration" "";
   Member "scala.concurrent.duration.Duration" "toMillis" ":";
   Member "scala.concurrent.duration.Duration$" "Inf" "";
   Member "scala.concurrent.duration.DurationConversions" "nanos" ":";
   Member "scala.concurrent.duration.package$" "DurationLong" "scala.Long:scala.Long";
   Member "scala.package$" "Left" "";
   Member "scala.package$" "List" "";
   Member "scala.package$" "Nil" "";
   Member "scala.package$" "Right" "";
   Member "scala.package$" "Vector" "";
   Member "scala.quoted" "Expr" "";
   Member "scala.quoted.Expr$" "apply" "1,java.lang.Object,scala.quoted.ToExpr,scala.quoted.Quotes:scala.quoted.Expr";
   Member "scala.quoted.Quotes" "reflect" "";
   Member "scala.quoted.Quotes.reflectModule" "Printer" "";
   Member "scala.quoted.Quotes.reflectModule" "TreeMethods" ":";
   Member "scala.quoted.Quotes.reflectModule" "asTerm" "scala.quoted.Expr:java.lang.Object";
   Member "scala.quoted.Quotes.reflectModule.PrinterModule" "TreeShortCode" ":";
   Member "scala.quoted.Quotes.reflectModule.TreeMethods" "show" "java.lang.Object,scala.quoted.Quotes.reflectModule.Printer:java.lang.String";
   Member "scala.quoted.ToExpr$" "StringToExpr" "1:scala.quoted.ToExpr$.StringToExpr";
   Member "scala.quoted.Type$" "of" "1,scala.quoted.Quotes:scala.quoted.Type";
   Member "scala.quoted.runtime.Expr$" "quote" "1,java.lang.Object:scala.Function1";
   Member "scala.quoted.runtime.Expr$" "splice" "1,scala.Function1:java.lang.Object";
   Member "scala.reflect.ClassTag" "runtimeClass" ":";
   Member "scala.reflect.ClassTag$" "apply" "1,java.lang.Class:scala.reflect.ClassTag";
   Member "scala.reflect.Enum" "ordinal" ":";
   Member "scala.runtime.ModuleSerializationProxy" "<init>" "java.lang.Class:scala.runtime.ModuleSerializationProxy";
   Member "scala.runtime.ScalaRunTime$" "_toString" "scala.Product:java.lang.String";
   Member "scala.util" "Failure" "";
   Member "scala.util" "Success" "";
   Member "scala.util.Either" "getOrElse" "1,scala.Function0:java.lang.Object";
   Member "scala.util.Either" "isLeft" ":";
   Member "scala.util.Either" "left" ":";
   Member "scala.util.Either" "map" "1,scala.Function1:scala.util.Either";
   Member "scala.util.Either$.LeftProjection" "getOrElse" "1,scala.Function0:java.lang.Object";
   Member "scala.util.Failure$" "apply" "1,java.lang.Throwable:scala.util.Failure";
   Member "scala.util.Left$" "apply" "2,java.lang.Object:scala.util.Left";
   Member "scala.util.Left$" "unapply" "2,scala.util.Left:scala.Option";
   Member "scala.util.Right$" "apply" "2,java.lang.Object:scala.util.Right";
   Member "scala.util.Right$" "unapply" "2,scala.util.Right:scala.Option";
   Member "scala.util.Success$" "apply" "1,java.lang.Object:scala.util.Success";
   Member "scala.util.Try" "get" ":";
   Member "scala.util.control" "NonFatal" "";
   Member "scala.util.control.NonFatal$" "unapply" "java.lang.Throwable:scala.Option";
   Member "scala.util.hashing" "MurmurHash3" "";
   Member "scala.util.hashing.MurmurHash3" "productHash" "scala.Product,scala.Int,scala.Boolean:scala.Int"].

Lemma kernel_surface_is : same (reaches_outside "ox" files kernel) kernel_surface = true.
Proof. vm_compute. reflexivity. Qed.

(** The JDK's part of it: what the contracts on the JDK's classes have to cover. *)
Definition of_jdk (s : sym) : bool :=
  match s with Member owner _ _ => String.prefix "java." owner | _ => false end.
Definition kernel_jdk : list sym := filter of_jdk kernel_surface.

package frflow.dsl.compiled.threads.known

import frflow.core.threads.Ty
import frflow.dsl.compiled.threads.known.JdkOp.On

/** The JDK as `Jdk.v` has it: the table from a class's method to its operation, and from a class to the type its
  * values are read at. A method that is not here is not read.
  */
object Jdk:
  private val atomic = "java.util.concurrent.atomic."
  private val future = "java.util.concurrent.CompletableFuture"
  private val nullable = Ty.option(Ty.Val)

  /** A class's method (`<init>`: its constructor) to its operation. */
  val methods: Map[(String, String), JdkOp] = Map(
    ("java.lang.Thread", "currentThread") -> JdkOp("CurrentThread", Nil, Ty.Tid, On.Absent),
    ("java.lang.Thread", "start") -> JdkOp("ThreadStart", List(Ty.Tid), Ty.Unit, On.First),
    ("java.lang.Thread", "interrupt") -> JdkOp("ThreadInterrupt", List(Ty.Tid), Ty.Unit, On.First),
    ("java.lang.Thread", "join") -> JdkOp("ThreadJoin", List(Ty.Tid), Ty.Unit, On.First),
    ("java.util.concurrent.ThreadFactory", "newThread") -> JdkOp("NewThread", List(Ty.Code), Ty.Tid, On.Absent),
    (atomic + "AtomicBoolean", "<init>") -> JdkOp("AbNew", List(Ty.Bool), Ty.Nat, On.Absent),
    (atomic + "AtomicBoolean", "get") -> JdkOp("AbGet", List(Ty.Nat), Ty.Bool, On.First),
    (atomic + "AtomicBoolean", "set") -> JdkOp("AbSet", List(Ty.Nat, Ty.Bool), Ty.Unit, On.First),
    (atomic + "AtomicBoolean", "getAndSet") -> JdkOp("AbGetAndSet", List(Ty.Nat, Ty.Bool), Ty.Bool, On.First),
    (atomic + "AtomicInteger", "<init>") -> JdkOp("AiNew", List(Ty.Z), Ty.Nat, On.Absent),
    (atomic + "AtomicInteger", "incrementAndGet") -> JdkOp("AiIncrementAndGet", List(Ty.Nat), Ty.Z, On.First),
    (atomic + "AtomicInteger", "decrementAndGet") -> JdkOp("AiDecrementAndGet", List(Ty.Nat), Ty.Z, On.First),
    (future, "<init>") -> JdkOp("CfNew", Nil, Ty.Nat, On.Absent),
    (future, "complete") -> JdkOp("CfComplete", List(Ty.Nat, Ty.Val), Ty.Bool, On.First),
    (future, "completeExceptionally") -> JdkOp("CfCompleteExceptionally", List(Ty.Nat, Ty.Exn), Ty.Bool, On.First),
    (future, "get") -> JdkOp("CfGet", List(Ty.Nat), Ty.Val, On.First),
    (future, "isCompletedExceptionally") -> JdkOp("CfIsCompletedExceptionally", List(Ty.Nat), Ty.Bool, On.First),
    (future, "exceptionNow") -> JdkOp("CfExceptionNow", List(Ty.Nat), Ty.Exn, On.First),
    (atomic + "AtomicReference", "<init>") -> JdkOp("ArNew", List(nullable), Ty.Nat, On.Absent),
    (atomic + "AtomicReference", "get") -> JdkOp("ArGet", List(Ty.Nat), nullable, On.First),
    (atomic + "AtomicReference", "getAndSet") -> JdkOp("ArGetAndSet", List(Ty.Nat, nullable), nullable, On.First),
    ("java.lang.ThreadLocal", "get") -> JdkOp("TlGet", List(Ty.Nat), nullable, On.First),
    ("java.lang.ThreadLocal", "set") -> JdkOp("TlSet", List(Ty.Nat, nullable), Ty.Unit, On.First),
    ("java.lang.Throwable", "addSuppressed") -> JdkOp("AddSuppressed", List(Ty.Exn, Ty.Exn), Ty.Unit, On.First))

  /** The class of the concurrent sets, and the method that makes one (`ConcurrentHashMap.newKeySet`). */
  val SetClass: String = "java.util.Set"
  val NewSet: (String, String) = ("java.util.concurrent.ConcurrentHashMap", "newKeySet")

  /** The three sets `Jdk.v` has, by what they hold: threads, exceptions, values. */
  private val sets: Map[Ty, String] = Map(Ty.Tid -> "Ts", Ty.Exn -> "Es", Ty.Val -> "Vs")

  /** A method of a concurrent set of `of`s: only a set of threads is removed from or asked. */
  def set(method: String, of: Ty): Option[JdkOp] = sets.get(of).flatMap(kind => (method, kind) match
    case ("newKeySet", _)  => Some(JdkOp(kind + "New", Nil, Ty.Nat, On.Absent))
    case ("add", _)        => Some(JdkOp(kind + "Add", List(Ty.Nat, of), Ty.Bool, On.First))
    case ("remove", "Ts")  => Some(JdkOp("TsRemove", List(Ty.Nat, of), Ty.Bool, On.First))
    case ("contains", "Ts") => Some(JdkOp("TsContains", List(Ty.Nat, of), Ty.Bool, On.First))
    case ("isEmpty", "Ts") => Some(JdkOp("TsIsEmpty", List(Ty.Nat), Ty.Bool, On.First))
    case _                 => None)

  /** The traversal (`forEach`) of a concurrent set of `of`s. */
  def traversal(of: Ty): Option[String] = sets.get(of).map(_ + "ForEach")

  /** A class to the type its values are read at: a thread is its id, an object with state a reference to it. */
  val types: Map[String, Ty] = Map("java.lang.Thread" -> Ty.Tid, "scala.Boolean" -> Ty.Bool, "scala.Unit" -> Ty.Unit,
    "scala.Int" -> Ty.Z, "scala.Nothing" -> Ty.Never, atomic + "AtomicBoolean" -> Ty.Nat,
    atomic + "AtomicInteger" -> Ty.Nat, atomic + "AtomicReference" -> Ty.Nat, future -> Ty.Nat,
    "java.lang.ThreadLocal" -> Ty.Nat, SetClass -> Ty.Nat)

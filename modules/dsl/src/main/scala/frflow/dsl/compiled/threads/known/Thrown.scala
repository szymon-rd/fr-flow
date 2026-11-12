package frflow.dsl.compiled.threads.known

/** A class of exceptions as a constructor of `exn` (`Jdk.v`): its name and, for each argument, the method of the
  * class that reads it and the name the argument is bound to where the exception is caught.
  */
final case class Thrown(ctor: String, fields: List[(String, String)])

object Thrown:
  val Throwable: String = "java.lang.Throwable"

  /** The classes `exn` has a constructor for; a throwable of another class read is `Other "<class>"`. */
  val classes: Map[String, Thrown] = Map(
    "java.lang.InterruptedException" -> Thrown("InterruptedException", Nil),
    "java.util.concurrent.ExecutionException" -> Thrown("ExecutionException", List("getCause" -> "cause")),
    "java.lang.IllegalStateException" -> Thrown("IllegalStateException", Nil),
    "java.lang.IllegalThreadStateException" -> Thrown("IllegalThreadStateException", Nil),
    "java.lang.NullPointerException" -> Thrown("NullPointerException", Nil),
    "java.util.NoSuchElementException" -> Thrown("NoSuchElementException", Nil))

  /** A throwable of a class `exn` has no constructor for. */
  val Other: String = "Other"

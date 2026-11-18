package ox.threads

/** What an assumption of the model is about: its kind. Each assumption says one (`.about(About.jdk)`); the README
  * lists the assumptions by it, and the suite reads from it what a root may rest on. In the order they are listed.
  */
object About:
  val jdk = "The JDK and the JVM"
  val objects = "Scala's objects"
  val use = "Who uses a herd"
  val factory = "The thread factory a herd is given"
  val privateField = "That a private field stays private"
  val readers = "Who reads a val"
  val variables = "That a variable stays its call's"
  val reach = "Who reaches a thread and the code startThread is given"
  val scopes = "Ox's scopes, which are not read"
  val time = "What happens in time"
  val forkCode = "The code a fork is given"
  val falseOfOx = "Ox itself, false of Ox 1.1.0"

  val all: List[String] =
    List(jdk, objects, use, factory, privateField, readers, variables, reach, scopes, time, forkCode, falseOfOx)

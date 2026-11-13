package frflow.project

import frflow.core.code.CodeFile
import frflow.core.name.RelPath
import frflow.project.code.{Governance, Governed, ModelFiles}

/** Which files are the model's own (owner §38, as before: a file holding nodes, code given a Definition, or the
  * FrModel; and one holding only vocabulary), and which need no node to govern them (also a file a program's body
  * refers to, holding only vocabulary and what it refers to). A file mixing vocabulary with plain code is governed
  * whole.
  */
class ModelFilesSuite extends munit.FunSuite:
  private val vocabulary = Set("Booking", "granted", "free", "storedBookings", "send", "mailerModel")

  test("a file of vocabulary only is the model's own: domain types, their companions, values, objects of them") {
    val domain = "package rooms\n\nimport frflow.*\n\n/** A booking. */\nfinal case class Booking(room: String) " +
      "derives RocqType\nobject Booking extends Data[Booking]\n\nval granted = Definition[Booking => Boolean](\"\")\n" +
      "val free = define { (b: Term[Booking]) =>\n  true }\n"
    val inObject = "package sharing\n\nobject Mailer:\n  val send = Definition[Int => Boolean](\"\")\n"
    assert(ModelFiles.only(domain, vocabulary) && ModelFiles.only(inObject, vocabulary))
  }

  test("a file mixing vocabulary with plain code is not; nor is one with an extension, nor an empty one") {
    val mixed = "package crm\n\nval granted = Definition[Int => Boolean](\"\")\n\n" +
      "final class SqliteDatabase(db: Db):\n  def load(): Int = db.load()\n"
    val extended = "package rooms\n\nval free = define { (b: Term[Int]) => true }\n" +
      "extension (b: Int) def twice = b * 2\n"
    assert(!ModelFiles.only(mixed, vocabulary) && !ModelFiles.only(extended, vocabulary))
    assert(!ModelFiles.only("package rooms\n", vocabulary))
  }

  test("a helper building terms counts as vocabulary; a plain def beside it still makes the file mixed") {
    val helpers = "package crm\n\nval granted = Definition[Int => Boolean](\"\")\n\n" +
      "def results(u: Term[Int],\n    q: Term[Int]): Term[List[Int]] =\n  someOf(u, q)\n" +
      "val held: Term[Int] = limit\nobject Steps:\n  def run(n: Term[Int]): Term[Boolean] = go(n)\n" +
      "  val pick: Term[Int] => Term[Boolean] = n => n > 0\n"
    val mixed = helpers + "def plain(n: Int): Int = n + 1\n"
    assert(ModelFiles.only(helpers, vocabulary), helpers)
    assert(!ModelFiles.only(mixed, vocabulary), mixed)
    assert(!ModelFiles.only("package crm\n\nval inferred = model.current\n", vocabulary))
    assertEquals(List("def f(a: Term[Int]): Term[Int] = a", "val x: Int = 1", "def g(n: Int) = n")
      .map(ModelFiles.resultType), List(Some("Term[Int]"), Some("Int"), None))
  }

  test("a helper's type is read with its brackets balanced: its final result is a term, or it is none") {
    assertEquals(List("Term[A]", "A => Term[B]", "(Term[A], Term[B]) => Term[List[C]]", "Term[A] => Term[B]",
      "Term[A] => IO[Unit]", "Term[A] => Future[B]", "Term[A] | Int", "IO[Term[A]]").map(ModelFiles.buildsTerms),
      List(true, true, true, true, false, false, false, false))
    val effect = "package crm\n\ndef deliver(t: Term[Int]): Term[Int] => IO[Unit] = _ => IO.unit\n"
    assert(!ModelFiles.only(effect, vocabulary), effect)
  }

  test("an object of helpers whose body also runs a statement is mixed: the statement is plain code") {
    val pure = "package crm\n\nobject Steps:\n  def run(n: Term[Int]): Term[Boolean] = go(n)\n" +
      "  val pick: Term[Int] => Term[Boolean] = n =>\n    n > 0\nend Steps\n"
    val running = pure.replace("end Steps", "  Registry.add(\"steps\")\nend Steps")
    assert(ModelFiles.only(pure, vocabulary), pure)
    assert(!ModelFiles.only(running, vocabulary), running)
  }

  test("a mixed file plain Scala refers to is governed whole; a file of the model's own, by the names it uses") {
    val (mixed, own) = (path("src/main/scala/crm/Mixed.scala"), path("src/main/scala/rooms/Domain.scala"))
    assertEquals(Governance.governed(Set(own), CodeFile(mixed, List("SqliteDatabase"))), Some(Governed.Whole(mixed)))
    assertEquals(Governance.governed(Set(own), CodeFile(own, List("free"))), Some(Governed.Named(own, List("free"))))
  }

  private def path(p: String): RelPath = RelPath.parse(p).getOrElse(fail(s"no path $p"))

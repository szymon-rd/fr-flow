package frflow.project

import frflow.core.code.CodeFile
import frflow.core.name.RelPath
import frflow.project.code.{Governance, Governed, ModelFiles}
import java.nio.file.Files
import scala.jdk.CollectionConverters.*
import scala.util.Using

/** Which files are the model's own (owner §38, as before: a file holding nodes, code given a Definition, or the
  * FrModel; and one holding only vocabulary), and which need no node to govern them (also a file a program's body
  * refers to, holding only vocabulary and what it refers to). A file mixing vocabulary with plain code is governed
  * whole.
  */
class ModelFilesSuite extends munit.FunSuite:
  private val vocabulary = Set("Booking", "granted", "free", "storedBookings", "send", "mailerModel")

  test("a file of vocabulary only is the model's own: domain types, their companions, values, objects of them") {
    val domain = "package rooms\n\nimport frflow.*\n\n/** A booking. */\nfinal case class Booking(room: String) " +
      "derives LeanType\nobject Booking extends Data[Booking]\n\nval granted = Definition[Booking => Boolean](\"\")\n" +
      "val free = define { (b: Term[Booking]) =>\n  true }\n"
    val inObject = "package sharing\n\nobject Mailer:\n  val send = Definition[Int => Flow[Unit]](\"\")\n\n" +
      "  object mailerModel extends StateModel[Int](\"\"):\n    send.means(_ => state.get.steps)\n"
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
      "val held: Term[Int] = model.current\nobject Steps:\n  def run(n: Term[Int]): Flow[Unit] = go(n)\n" +
      "  val pick: Term[Int] => Term[Boolean] = n => n > 0\n"
    val mixed = helpers + "def plain(n: Int): Int = n + 1\n"
    assert(ModelFiles.only(helpers, vocabulary), helpers)
    assert(!ModelFiles.only(mixed, vocabulary), mixed)
    assert(!ModelFiles.only("package crm\n\nval inferred = model.current\n", vocabulary))
    assertEquals(List("def f(a: Term[Int]): Term[Int] = a", "val x: Int = 1", "def g(n: Int) = n")
      .map(ModelFiles.resultType), List(Some("Term[Int]"), Some("Int"), None))
  }

  test("crm: Domain.scala, vocabulary and helpers building terms, is the model's own; its SQLite code is not") {
    val t = Projects.elaborated(_root_.crm.knowledge).theory
    val sources = Using.resource(Files.walk(Projects.base.resolve("examples/crm/src/main")))(_.iterator.asScala
      .toList).filter(p => p.toString.endsWith(".scala"))
      .map(p => path(Projects.base.relativize(p).toString) -> Files.readString(p)).toMap
    val own = ModelFiles.accounted(t, sources)
    val at = "examples/crm/src/main/scala/crm/"
    assert(own(path(at + "Domain.scala")), own)
    assertEquals(List("Db", "Events", "History", "MemoryDatabase").filter(n => own(path(at + n + ".scala"))), Nil)
  }

  test("a mixed file plain Scala refers to is governed whole; a file of the model's own, by the names it uses") {
    val (mixed, own) = (path("src/main/scala/crm/Mixed.scala"), path("src/main/scala/rooms/Domain.scala"))
    assertEquals(Governance.governed(Set(own), CodeFile(mixed, List("SqliteDatabase"))), Some(Governed.Whole(mixed)))
    assertEquals(Governance.governed(Set(own), CodeFile(own, List("free"))), Some(Governed.Named(own, List("free"))))
  }

  test("sharing: Delivery, a program's steps, needs no node and is not the model's own; Mailer, vocabulary, is; " +
    "the SQLite store is neither") {
    // As the model records them: relative to the build.
    val t = Projects.elaborated(_root_.sharing.knowledge).theory
    val sources = Using.resource(Files.walk(Projects.base.resolve("examples/sharing/src/main")))(_.iterator.asScala
      .toList).filter(p => p.toString.endsWith(".scala"))
      .map(p => path(Projects.base.relativize(p).toString) -> Files.readString(p)).toMap
    val (own, accounted) = (ModelFiles.own(t, sources), ModelFiles.accounted(t, sources))
    val at = "examples/sharing/src/main/scala/sharing/"
    val (delivery, mailer, store) = (path(at + "notifications/Delivery.scala"), path(at + "notifications/Mailer.scala"),
      path(at + "store/SqliteLibraryStore.scala"))
    assert(t.own.referred.get(delivery).exists(_.contains("Delivery")), t.own.referred)
    assertEquals((own(delivery), accounted(delivery)), (false, true))
    assertEquals((own(mailer), accounted(mailer)), (true, true))
    assertEquals((own(store), accounted(store)), (false, false))
  }

  private def path(p: String): RelPath = RelPath.parse(p).getOrElse(fail(s"no path $p"))

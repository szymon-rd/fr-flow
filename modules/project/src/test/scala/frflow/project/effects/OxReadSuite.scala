package frflow.project.effects

import frflow.dsl.compiled.normal.Normalise

/** How much of the Ox code the Ox model rests on is read into normalised Scala: each method of the five files,
  * and why it is not read where it is not. The numbers are the measure the reading is extended by.
  */
class OxReadSuite extends munit.FunSuite:
  private val files = Set("ox/internal/ThreadHerd.tasty", "ox/OxError.tasty", "ox/unsupervised$package.tasty",
    "ox/supervised$package.tasty", "ox/fork$package.tasty")

  private lazy val surveyed = Normalise.survey(classOf[ox.Ox], path => files.exists(path.endsWith))

  /** Why the methods that are not read are not, most frequent first, with some of the methods. */
  private def reasons: List[String] =
    surveyed.collect { case (method, Some(why)) => why.linesIterator.next() -> method }.groupBy(_._1).toList
      .sortBy((why, ms) => (-ms.size, why))
      .map((why, ms) => s"${ms.size} $why :: ${ms.map(_._2).take(5).mkString(", ")}")

  test("of the 58 methods of the five files, 7 are read") {
    sys.env.get("OXREAD_OUT").foreach(out =>
      java.nio.file.Files.writeString(java.nio.file.Path.of(out), reasons.mkString("\n")): Unit)
    assertEquals((surveyed.size, surveyed.count(_._2.isEmpty)), (58, 7))
  }

  test("what is not read is refused for a reason that is said") {
    assert(reasons.exists(_.contains("a method that takes types")), reasons)
    assert(reasons.exists(_.contains("what is passed by name")), reasons)
  }

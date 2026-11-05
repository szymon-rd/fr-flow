package frflow.api

import frflow.api.fixture.Opened
import frflow.api.shell.Relocate
import frflow.api.view.Warning
import frflow.core.name.RelPath
import java.nio.file.Path

/** A project under a directory of the build (`examples/NAME`, as `init` makes it): the files its model records are
  * read relative to the build, made relative to the project, so its own model file is not warned ungoverned.
  */
class RelocateSuite extends munit.CatsEffectSuite:
  private val e = Opened.before.model
  private val recorded = e.theory.nodes.map(_.at.file).headOption.getOrElse(fail("no node"))
  /** The directory the shelf's test sources are under, as a project's would be (`modules/api`, under the build). */
  private val project = recorded.value.take(recorded.value.indexOf("src/"))
  private val moved = Relocate(e, Path.of(""), Path.of("").toAbsolutePath.resolve(project))

  test("each file the model records is made relative to the project's directory") {
    assert(project.nonEmpty, recorded)
    assertEquals(moved.theory.nodes.map(_.at.file.value).distinct, List(recorded.value.drop(project.length)))
    assertEquals(moved.theory.code.attached.values.map(_.writtenIn.value).toList.distinct,
      List(recorded.value.drop(project.length)))
    assertEquals(Relocate(e, Path.of("/elsewhere"), Path.of("/build/examples/toy")).theory.nodes.map(_.at.file),
      e.theory.nodes.map(_.at.file))
  }

  test("the files code refers to are made relative to the project too: rooms' calendar, its table's Scala") {
    val rooms = Relocate(frflow.project.Projects.rooms, Path.of(""), Path.of("").toAbsolutePath.resolve("examples/rooms"))
    val tested = rooms.theory.code.attached.values.flatMap(_.code.scala).flatMap(_.files).map(_.path.value).toList
    val modelled = rooms.theory.code.implemented.values.flatMap(_.files).map(_.path.value).toList
    assert(tested.contains("src/main/scala/rooms/Calendar.scala"), tested)
    assert(modelled.contains("src/main/scala/rooms/BookingsTable.scala"), modelled)
  }

  test("the project's own model file is not ungoverned once relocated; as recorded it would be") {
    val file = moved.theory.nodes.map(_.at.file).headOption.getOrElse(fail("no node"))
    val sources = RelPath.parse("src/test").getOrElse(fail("no path"))
    def ungoverned(p: Project) = Opened.ports(Map(file -> "object Shelf"))
      .flatMap(Opened.over(p, _)).flatMap(_.reading.view).map(_.warnings.collect { case w: Warning.Ungoverned => w })
    for
      relocated <- ungoverned(Opened.before.copy(model = moved, sources = List(sources)))
      asIs      <- ungoverned(Opened.before.copy(sources = List(sources)))
    yield
      assertEquals(relocated, Nil)
      assertEquals(asIs, List(Warning.Ungoverned(file)))
  }

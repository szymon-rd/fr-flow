package frflow.cli.found

import frflow.api.fixture.Opened
import frflow.api.view.NotMade
import frflow.cli.command.Command
import frflow.cli.{Cli, TestClasses}
import java.nio.file.Path

/** The classes of examples `check` finds among a project's test classes: each it can make is read, and `status` warns
  * of each it cannot, saying why, so no example is dropped unsaid.
  */
class FoundSuite extends munit.CatsEffectSuite:
  private val found = TestClasses.in(Path.of(getClass.getProtectionDomain.getCodeSource.getLocation.toURI))
  private val ours = found.unread.filter(_._1.startsWith("frflow.cli.found.")).toMap

  test("a class it can make is read; one with no constructor without arguments, nested, or throwing is not") {
    assert(found.examples.exists(_.getClass.getName == "frflow.cli.found.Found$Made"), found.examples)
    assertEquals(ours.keySet, Set("frflow.cli.found.Given", "frflow.cli.found.Found$Outer$Inner",
      "frflow.cli.found.Throwing"))
    assertEquals((ours("frflow.cli.found.Given"), ours("frflow.cli.found.Found$Outer$Inner")),
      (NotMade.NoConstructor, NotMade.Nested))
    assert(ours("frflow.cli.found.Throwing") match
      case NotMade.Threw(m) => m.contains("no model here")
      case _                => false, ours)
  }

  test("status warns of each class of examples not read, and why") {
    Opened.api(Opened.before.copy(unread = ours.toList.sortBy(_._1))).flatMap(Cli.all(_, Command.Status(json = false)))
      .map { (_, text) =>
        assert(text.contains("warning: the examples of frflow.cli.found.Given are not read: it has no constructor " +
          "without arguments (add `def this() = this(knowledge)`)"), text)
        assert(text.contains("the examples of frflow.cli.found.Found$Outer$Inner are not read: it is nested"), text)
        assert(text.contains("the examples of frflow.cli.found.Throwing are not read: making it threw"), text)
      }
  }

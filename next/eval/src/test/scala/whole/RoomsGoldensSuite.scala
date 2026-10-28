package whole

import frflow.core.name.{DefName, KbName}
import frflow.proof.layout.{Laid, Layout}
import frflow.proof.lean.ast.ModuleName
import frflow.proof.lean.print.Print
import frflow.proof.obligation.AlwaysSuite
import java.nio.file.{Files, Path}

/** Rooms' Lean as the port prints it, byte for byte (`next/proof/src/test/resources/rooms`, owner §25: one type,
  * `Booking`): the boundary, its model and `World`; booking's run on the models; and every `keeps_` and `makes_` the
  * obligations declare. With `FRFLOW_GOLDEN` set, they are written there instead.
  */
class RoomsGoldensSuite extends munit.FunSuite:
  private val r = Theories.resolved(rooms.rooms)
  private val laid = Laid(r, Map.empty, Nil)
  private val layout = Layout(KbName("Rooms"))

  private def module(name: ModuleName): String =
    laid.modules.find(_.name == name).map(Print.module).getOrElse(fail(s"no module $name"))

  private def same(path: String, printed: String): Unit = sys.env.get("FRFLOW_GOLDEN") match
    case Some(dir) =>
      Files.createDirectories(Path.of(dir, path).getParent)
      Files.writeString(Path.of(dir, path), printed): Unit
    case None      =>
      assertNoDiff(printed, scala.io.Source.fromResource(s"rooms/$path", getClass.getClassLoader)(
        using scala.io.Codec.UTF8).mkString)

  test("Boundaries.lean: the table's class, its model, World, the instance and its lemmas") {
    same("Boundaries.lean", module(layout.boundaries))
  }

  test("Domain/Def_bookIfGranted_run.lean: booking's run on the models, of a Booking") {
    same("Domain/Def_bookIfGranted_run.lean", module(layout.define(DefName("bookIfGranted_run"))))
  }

  test("Always.lean: what each run of book keeps, and what inRoom makes, over Bookings meeting the rules") {
    same("Always.lean", AlwaysSuite().declared(laid, r))
  }

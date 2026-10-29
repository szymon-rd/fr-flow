package frflow.proof.obligation

import frflow.proof.layout.{Broken, Laid, Lowering, Mini, MiniProject, Programs, ProgramsProject}
import frflow.proof.layout.failing.Failing
import frflow.proof.lean.lower.LowerKeeps
import frflow.proof.lean.print.PrintDecl

/** What `cover_` and `made_` state, byte for byte (`resources/always`): every run of a program writing a store keeps
  * what always holds of its values (`keeps_<op>`), and every result of a define, a program and a store's operation
  * meets it (`makes_<maker>`), and what proven code hands plain Scala at each call meets it
  * (`makes_<code>_call_<i>`), each over inputs and worlds meeting every `always`. Rooms' are pinned where rooms is
  * (`whole.RoomsGoldensSuite`, owner §25). With `FRFLOW_GOLDEN` set, they are written there instead.
  */
class AlwaysSuite extends munit.FunSuite:
  private def same(path: String, printed: String): Unit = sys.env.get("FRFLOW_GOLDEN") match
    case Some(dir) =>
      java.nio.file.Files.createDirectories(java.nio.file.Path.of(dir, path).getParent)
      java.nio.file.Files.writeString(java.nio.file.Path.of(dir, path), printed): Unit
    case None      =>
      assertEquals(printed, scala.io.Source.fromResource(path, getClass.getClassLoader)(using scala.io.Codec.UTF8)
        .mkString)

  /** Every `keeps_`/`makes_` a theory's obligations declare, in the order its nodes ask them. */
  def declared(laid: Laid, r: frflow.core.analysis.Resolved): String =
    val l = Lowering(r, laid.table)
    val keeps = LowerKeeps(l.env, l.table, l.naming)
    def stated(p: Prop): List[Prop] = p match
      case k: Prop.Keeps     => List(k)
      case m: Prop.Makes     => List(m)
      case Prop.Forall(_, b) => stated(b)
      case Prop.Implies(_, c) => stated(c)
      case _                 => Nil
    laid.nodes.flatMap(_.required).flatMap(o => stated(o.goal)).map {
      case k: Prop.Keeps => PrintDecl(keeps(k))
      case m: Prop.Makes => PrintDecl(keeps.makes(m))
      case _             => ""
    }.mkString("", "\n\n", "\n")

  test("Mini: every run of book keeps endsAfterStart and fromTheForm, from a world and an input meeting each") {
    same("always/Mini.lean", declared(MiniProject, Mini.resolved))
  }

  test("Programs: every result of a define, of programs (one with no inputs) and of a store's operation meets them") {
    same("always/Programs.lean", declared(ProgramsProject, Programs.resolved))
  }

  test("Broken: what misdate makes and what fileBackwards stores is stated of, as of any other") {
    same("always/Broken.lean", declared(Laid(Broken.resolved, Map.empty, Nil), Broken.resolved))
  }

  test("Failing: a run of a program that may fail keeps them whether it succeeds or fails; what it makes is of the " +
    "runs that succeed") {
    same("always/Failing.lean", declared(Laid(Failing.resolved, Map.empty, Nil), Failing.resolved))
  }

package frflow.proof.obligation

import frflow.proof.layout.{Broken, Laid, Lowering, Mini, MiniProject, Programs, ProgramsProject}
import frflow.proof.layout.failing.Failing
import frflow.proof.lean.lower.LowerKeeps
import frflow.proof.lean.print.PrintDecl

/** What `cover_` and `made_` state, byte for byte (`resources/always`): every run of a program writing a store keeps
  * what always holds of its values (`keeps_<op>`), and every result of a define, a program and a store's operation
  * meets it (`makes_<maker>`), each over inputs and worlds meeting every `always`. The rooms goldens are §21's.
  */
class AlwaysSuite extends munit.FunSuite:
  private def golden(path: String): String =
    scala.io.Source.fromResource(path, getClass.getClassLoader)(using scala.io.Codec.UTF8).mkString

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
    assertEquals(declared(MiniProject, Mini.resolved), golden("always/Mini.lean"))
  }

  test("Programs: every result of a define, of programs (one with no inputs) and of a store's operation meets them") {
    assertEquals(declared(ProgramsProject, Programs.resolved), golden("always/Programs.lean"))
  }

  test("Broken: what misdate makes and what fileBackwards stores is stated of, as of any other") {
    assertEquals(declared(Laid(Broken.resolved, Map.empty, Nil), Broken.resolved), golden("always/Broken.lean"))
  }

  test("Failing: a run of a program that may fail keeps them whether it succeeds or fails; what it makes is of the " +
    "runs that succeed") {
    assertEquals(declared(Laid(Failing.resolved, Map.empty, Nil), Failing.resolved), golden("always/Failing.lean"))
  }

  test("the rooms goldens state §21's: requests from the form, meeting fromTheForm") {
    List("Keeps_endsAfterStart.decl.lean", "Keeps_neverOverlap.decl.lean", "Def_bookIfGranted_run.decl.lean")
      .foreach(f => assert(golden(s"rooms/$f").contains("Request"), f))
    assert(golden("rooms/Keeps_endsAfterStart.decl.lean").contains("(Rooms.fromTheForm request)"))
  }

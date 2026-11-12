package frflow.project.program

import cats.effect.IO
import frflow.core.name.NodeId
import frflow.decision.review.Unproven
import frflow.project.{Live, Ported, Projects}
import frflow.project.check.CheckProgram
import frflow.project.pipeline.{Analysis, ReadProof}
import frflow.project.port.RunCode
import frflow.project.port.memory.ScriptedProver
import frflow.proof.layout.Notation

import frflow.proof.obligation.ObligationName
import frflow.proof.verdict.{ObligationStatus, Result}
import scala.concurrent.duration.*
import whole.Seeded

/** The step 12 review's seeded bugs, each kept red: a consistency statement has the code standing for a Definition
  * reached only through other code, so no proof chooses its meaning (B1); statements pinning one provided value
  * apart are one group, which no witness meets (S1); a step over what a maker makes rests on what the maker's callee
  * makes too (S2).
  */
class SeededSuite extends munit.CatsEffectSuite:
  override val munitIOTimeout: Duration = 60.minutes

  private def whole(a: Analysis): String = a.modules.find(_.name.dotted.endsWith("Whole.Spec")).map(Notation.module)
    .getOrElse(fail("no whole statements"))

  test("a consistency statement has inner's code stand in it, reached only through outer's, and never binds it") {
    val spec = whole(Projects.bare(Projects.elaborated(Seeded.Hidden.knowledge)))
    val stated = spec.linesIterator.dropWhile(!_.contains("def consistent_0 ")).slice(1, 2).mkString
    assert(stated.contains("(Hidden.through Hidden.twice)") && !stated.contains("(inner :"), stated)
  }

  /** Makers checked with Rocq scripted: every obligation proven but the `made_` named. */
  private def kept(m: Makers, failing: String*): IO[List[Unproven]] =
    for
      p    <- Projects.inMemory(Map.empty)
      a    <- Projects.analysed(p, Projects.elaborated(m.knowledge), Nil)
      lake <- ScriptedProver[IO](Scripted(a, failing.toSet, Set.empty).answer, installed = true)
      out  <- CheckProgram(p.files, lake, RunCode.inline[IO])(a, None)
    yield out._2.decided.theory.node(NodeId("top")).fold(fail("no top"))(n => ReadProof.of(out._2, n).unproven)
      .collect { case k @ Unproven.Kept(_) => k }

  test("a step over what outer makes is unproven while outer, or inner which it calls, breaks the rule") {
    for
      direct   <- kept(Makers("Direct", false), "made_outer")
      indirect <- kept(Makers("Indirect", true), "made_inner")
      sound    <- kept(Makers("Indirect", true))
    yield
      assert(direct.contains(Unproven.Kept(NodeId("noDups"))), direct)
      assert(indirect.contains(Unproven.Kept(NodeId("noDups"))), indirect)
      assertEquals(sound, Nil)
  }

  private def consistent(a: Analysis): Map[ObligationName, ObligationStatus] =
    a.wholeCheck.toList.flatMap(_.results).collect { case Result(n @ ObligationName.Consistent(_), s, _) => n -> s }
      .toMap

  test("a provided value the standing code reaches is universal in its group, given what the world says of it") {
    val spec = whole(Projects.bare(Projects.elaborated(Seeded.Through.knowledge)))
    val stated = spec.linesIterator.dropWhile(!_.contains("def consistent_0 ")).slice(1, 2).mkString
    assert(stated.startsWith("  ∀ (k : Int), (Through.kPositive.claim k) → (∃ (holds : ") &&
      stated.contains("(Through.through (Through.maybe k))"), stated)
  }

  test("an assumption false of the code its words mean is not proven of it, and the root over it stays red".tag(Live)) {
    Ported.run(Projects.elaborated(Seeded.Trusted.knowledge), Nil, Nil).map { r =>
      val unproven = Ported.unproven(r)
      assert(unproven.contains("outerKeeps") && unproven.contains("emptyHoldsNothing"), Ported.table(r))
    }
  }

  test("an assumption with no word at all is proven or red: no list 3 long red, none -1 long proven".tag(Live)) {
    def unproven(p: Seeded.Pure) = Ported.run(Projects.elaborated(p.knowledge), Nil, Nil)
      .map(r => Ported.unproven(r).get("noDouble"))
    for
      three <- unproven(Seeded.Pure(3))
      none  <- unproven(Seeded.Pure(-1))
    yield
      assert(three.nonEmpty, three)
      assertEquals(none, None)
  }

  test("two assumptions pinning n apart are one group, not proven".tag(Live)) {
    Ported.run(Projects.elaborated(Seeded.TwoPins.knowledge), Nil, Nil).map { r =>
      assertEquals(r.groups.map(_._1), List(0))
      assertNotEquals(consistent(r).get(ObligationName.Consistent(0)), Some(ObligationStatus.Proven))
    }
  }

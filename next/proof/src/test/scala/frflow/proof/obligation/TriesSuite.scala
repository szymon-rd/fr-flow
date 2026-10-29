package frflow.proof.obligation

import frflow.core.name.NodeId
import frflow.proof.layout.Mini
import frflow.proof.lean.lower.LowerObligation
import frflow.proof.lean.print.PrintDecl
import frflow.proof.obligation.tried.{Idle, Tries}
import frflow.proof.reading.ObligationNames
import frflow.proof.terms.TermTable

/** One test per try (`Tries`, `Idle`): each asked where its shape is, with its statement and sentence, read back by
  * its name.
  */
class TriesSuite extends munit.FunSuite:
  private lazy val table = TermTable.of(Pair.resolved)
  private def tries(n: String): List[Obligation] = Tries.of(Pair.resolved, table, NodeId(n))
  private def kinds(n: String): List[TryKind] = tries(n).map(_.name).collect { case ObligationName.Tried(k) => k }
  private def lean(n: String, k: TryKind): String =
    PrintDecl(LowerObligation(frflow.proof.layout.Lowering(Pair.resolved, table).props)(
      tries(n).find(_.name == ObligationName.Tried(k)).getOrElse(fail(s"no $k of $n"))))
  private val (aboutF, aboutG) = (NodeId("aboutF"), NodeId("aboutG"))

  test("needed_C: of a split, each part left out in turn") {
    assertEquals(kinds("both").take(2), List(TryKind.Needed(aboutF), TryKind.Needed(aboutG)))
    assert(lean("both", TryKind.Needed(aboutF)).contains("∀ (f : Int → Prop) (g : Int → Prop), ∀ (h_aboutG : " +
      "(Test.aboutG.claim g)), (Test.both.claim f g)"), lean("both", TryKind.Needed(aboutF)))
  }

  test("restates_i_C: each part against each conjunct, when there are as many conjuncts as parts") {
    assertEquals(kinds("both").slice(2, 6), List(TryKind.RestatesConjunct(aboutF, 1), TryKind.RestatesConjunct(aboutF,
      2), TryKind.RestatesConjunct(aboutG, 1), TryKind.RestatesConjunct(aboutG, 2)))
    assert(lean("both", TryKind.RestatesConjunct(aboutG, 2)).contains(
      "((Test.aboutG.claim g) ↔ (Test.both.conjunct_2 f g))"), lean("both", TryKind.RestatesConjunct(aboutG, 2)))
  }

  test("vacuous and restates: of a node with one part") {
    assertEquals(kinds("same").take(2), List(TryKind.Vacuous, TryKind.Restates))
    assertEquals(tries("same").take(2).map(_.doc),
      List("same holds whatever aboutF says.", "aboutF follows from same."))
  }

  test("clash and unsat: fatal, each asked of every split and every node") {
    assert(kinds("both").contains(TryKind.Clash) && kinds("same").contains(TryKind.Clash))
    assertEquals(kinds("aboutF"), List(TryKind.Unsat))
    assert(TryKind.Clash.fatal && TryKind.Unsat.fatal && !TryKind.Vacuous.fatal)
    assert(lean("aboutF", TryKind.Unsat).contains("∀ (f : Int → Prop), ¬ (Test.aboutF.claim f)"))
  }

  test("idle: a root met by every Definition it names doing nothing, within Lean's default budget") {
    val coded = Pair.withDefinitions
    val ofIt = Tries.of(coded, TermTable.of(coded), NodeId("both")).filter(_.name == ObligationName.Tried(TryKind.Idle))
    assertEquals(ofIt.map(_.discharge), List(Discharge.Attempt(Idle.DefaultHeartbeats)))
    val printed = PrintDecl(LowerObligation(frflow.proof.layout.Lowering(coded, TermTable.of(coded)).props)(ofIt.head))
    assert(printed.contains("(Test.both.claim (fun (x0 : Int) => False) (fun (x0 : Int) => False))"), printed)
    assertEquals(kinds("aboutF").filter(_ == TryKind.Idle), Nil)
  }

  test("idle: none of a root naming only Declarations, which are no code to do nothing") {
    assertEquals(kinds("both").filter(_ == TryKind.Idle), Nil)
  }

  test("every try's name reads back as the try") {
    (tries("both") ++ tries("same")).foreach(o =>
      assertEquals(ObligationNames.read(LowerObligation.name(o.name).text), Some(o.name)))
  }

  test("a one-part node's tries, as Mini's allowsOne, over a Declaration, has them") {
    assertEquals(Tries.of(Mini.resolved, TermTable.of(Mini.resolved), NodeId("allowsOne")).map(_.name),
      List(TryKind.Vacuous, TryKind.Restates, TryKind.Clash, TryKind.Unsat).map(ObligationName.Tried(_)))
  }

package frflow.proof.prover.laws

import frflow.core.Booking
import frflow.core.expr.{LawSeeds, Terms, Tm}
import frflow.core.term.language.Final
import frflow.proof.prover.ast.{LExpr, Syntax}
import frflow.proof.prover.ast.Tree.into
import frflow.proof.prover.lower.{Identifiers, Naming, Seen}
import frflow.proof.prover.term.{Notation, Print, Printed, Shaped}

/** The lowering is one for every syntax (`Syntax[E]`, `Seen[E]`): a term written straight into the notation, each
  * text kept with what it is (`Shaped`), is the text of the tree written first and read after. So the tree is one
  * interpreter among the others, the form a module is kept in, and nothing the lowering needs.
  */
class SyntaxLawsSuite extends munit.FunSuite:
  private val naming = Naming.over(Set.empty, Set(Booking.name.value, MoreTerms.eventName.value, "World"))
  private val terms: List[Final[Boolean]] =
    LawSeeds(300).flatMap(seed => List(Tm.closed(Terms(seed).bool(3, 0)), MoreTerms(seed).formula))
  private given Syntax[String] = Notation

  test("a term written straight into the notation is the text of its tree") {
    terms.foreach { t =>
      val tree = Printed.formula[LExpr, Boolean](LawsEnv.env, naming)(t)
      val direct = Printed.formula[Shaped[String], Boolean](LawsEnv.env, naming)(t)
      assertEquals(direct.e, Print.expr(tree))
    }
  }

  test("what a text is kept with is what its tree shows: the identifiers it names") {
    terms.foreach { t =>
      val tree = Printed.formula[LExpr, Boolean](LawsEnv.env, naming)(t)
      val direct = Printed.formula[Shaped[String], Boolean](LawsEnv.env, naming)(t)
      assertEquals(direct.names, summon[Seen[LExpr]].names(tree))
      assertEquals(tree.into(Identifiers), direct.names)
    }
  }

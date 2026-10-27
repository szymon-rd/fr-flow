package frflow.api

import cats.kernel.laws.discipline.CommutativeMonoidTests
import frflow.api.Opened.id
import frflow.api.derive.Leans
import frflow.api.view.{Tally, View, Views}
import frflow.proof.verdict.{CheckStatus, ObligationStatus}
import munit.DisciplineSuite
import org.scalacheck.{Arbitrary, Gen}

/** What front ends print of a view, each a function of it: the tree, the inbox, the parts beside a node; the counts
  * are a commutative monoid; and every state Lean gives has its view.
  */
class ViewsSuite extends munit.CatsEffectSuite with DisciplineSuite:
  private val (nonNegative, sameAbove) = (id("nonNegative"), id("sameAbove"))
  private def shelf = Opened.api(Opened.before).flatMap(_.reading.view)

  given Arbitrary[Tally[Boolean]] = Arbitrary(Gen.mapOf(Gen.zip(Arbitrary.arbitrary[Boolean], Gen.choose(0, 50)))
    .map(Tally(_)))
  given cats.Eq[Tally[Boolean]] = cats.Eq.by(t => List(true, false).map(t(_)))
  checkAll("Tally", CommutativeMonoidTests[Tally[Boolean]].commutativeMonoid)

  test("the tree: the roots, each node under its first parent, its children in the order of its parts") {
    shelf.map { v =>
      assertEquals(Views.tree(v, None), List(0 -> nonNegative, 1 -> sameAbove))
      assertEquals(Views.tree(v, Some(sameAbove)), List(0 -> sameAbove))
      assertEquals(Views.tree(v, Some(id("dragons"))), Nil)
    }
  }

  test("the tree draws each node once, a premise under no parent after the roots") {
    Opened.api(Opened.trusted).flatMap(_.reading.view).map { (v: View) =>
      assertEquals(Views.tree(v, None).map(_._2), List(id("aboveMinusOne"), id("nonNegative")))
      assertEquals(Views.tree(v, None).map(_._2).distinct.size, v.nodes.size)
    }
  }

  test("the inbox: what waits for the developer in decision order, less what a layer holds back") {
    shelf.map { v =>
      assertEquals(Views.inbox(v, Set.empty), List(nonNegative, sameAbove))
      assertEquals(Views.inbox(v, Set(sameAbove)), List(nonNegative))
    }
  }

  test("beside a node: under each parent, the other parts that with it make the parent") {
    shelf.map(v => assertEquals(Views.beside(v, sameAbove), List(nonNegative -> Nil)))
  }

  test("every state Lean gives a check or an obligation has its view, of the same name") {
    assertEquals(CheckStatus.values.toList.map(s => Leans.state(s).toString), CheckStatus.values.toList.map(_.toString))
    assertEquals(ObligationStatus.values.toList.map(s => Leans.state(s).toString),
      ObligationStatus.values.toList.map(_.toString))
  }

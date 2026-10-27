package frflow.web

import frflow.api.view.Warning
import frflow.decision.rules.Refusal
import scala.compiletime.constValueTuple
import scala.deriving.Mirror

/** The page says every refusal and every warning in words of its own, none in the raw words of its type. */
class PageSuite extends munit.FunSuite:
  private val page = scala.io.Source.fromResource("frflow/web/index.html").mkString

  private inline def cases[A](using m: Mirror.SumOf[A]): List[String] =
    constValueTuple[m.MirroredElemLabels].toList.map(_.toString)

  /** The names the page's map from `start` to the first `}` that ends a line names. */
  private def named(start: String): Set[String] =
    val from = page.indexOf(start)
    assert(from >= 0, start)
    val block = page.substring(from, page.indexOf("};", from))
    raw"(\w+):".r.findAllMatchIn(block).map(_.group(1)).toSet

  test("each refusal has its words on the page") {
    assertEquals(cases[Refusal].filterNot(named("const refusals = {")), Nil)
  }

  test("each warning has its words on the page") {
    assertEquals(cases[Warning].filterNot(named("const says = {")), Nil)
  }

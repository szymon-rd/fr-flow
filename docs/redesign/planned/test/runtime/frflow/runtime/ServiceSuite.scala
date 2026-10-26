package frflow.runtime

import frflow.core.Elaborated
import frflow.core.name.{NodeId, SymbolName}
import frflow.eval.{Compiled, ScalaValue}
import frflow.eval.run.{Assumes, Broken, Echo}
import frflow.runtime.check.{AssumptionWatch, CallValues}
import java.util.concurrent.atomic.AtomicInteger
import scala.collection.mutable.ListBuffer

/** A contract's code where it runs (today's `enforce`): the call check, then the assumption watch. */
class ServiceSuite extends munit.FunSuite:
  test("a result that breaks the post is reported, then thrown") {
    val wrong: String => String = _ => "wrong"
    val reported = ListBuffer.empty[Violation]
    val echo = Running(Elaborated(Echo.theory(wrong), Map.empty, Nil), v => reported.append(v))
      .wired(Echo.contract, Nil).map(_.as[String => String]).getOrElse(fail("Echo is wired"))
    val thrown = intercept[ContractViolation](echo("hi"))
    assertEquals(thrown.violation,
      Violation(Echo.contract, Broken.Post, List(ScalaValue("hi")), Some(ScalaValue("wrong"))))
    assertEquals(reported.toList, List(thrown.violation))
  }

  test("an outside system's adapter called from a contract's code is checked on each of its calls") {
    val sqlBug: String => String = q => if q == "x' OR 1=1" then "every record" else q
    val reported = ListBuffer.empty[Violation]
    val search = Running(Elaborated(Search.theory(Some(sqlBug)), Map.empty, Nil), v => reported.append(v))
      .wired(Search.contract, Nil).map(_.as[String => String]).getOrElse(fail("Search is wired"))
    assertEquals(search("ada"), "ada")
    val thrown = intercept[ContractViolation](search("x' OR 1=1"))
    assertEquals(thrown.violation,
      Violation(Search.assumption, Broken.Post, List(ScalaValue("x' OR 1=1")), Some(ScalaValue("every record"))))
    assertEquals(reported.toList, List(thrown.violation))
  }

  test("an operation the code calls, with neither code nor a binding, is reported when the service is wired") {
    val wired = Running(Elaborated(Search.theory(None), Map.empty, Nil), _ => ()).wired(Search.contract, Nil)
    assertEquals(wired.map(_ => ()), Left(WiringError.Unbound(Search.contract, List(Search.fetch))))
  }

  test("an assumption is checked again only when a value it reads changed") {
    val limit = SymbolName("limit")
    val checks = AtomicInteger(0)
    val counted = Compiled { _ =>
      val _ = checks.incrementAndGet()
      Right(ScalaValue(true))
    }
    val watch = AssumptionWatch(List(Assumes(NodeId("LimitIsSet"), List(limit), counted)))
    def call(v: String): Option[NodeId] =
      val now = CallValues(Map(limit -> (() => v)))
      val _ = now.value(limit)
      watch.broken(now)
    assertEquals(List("a", "a", "b", "b", "a").flatMap(call), Nil)
    assertEquals(checks.get, 3)
  }

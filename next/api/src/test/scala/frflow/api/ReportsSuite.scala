package frflow.api

import cats.syntax.all.*
import frflow.api.Opened.id
import frflow.api.view.Found
import frflow.core.name.RelPath
import frflow.decision.review.Unproven

/** What the developer reads to know where things stand (today's `ReportsSuite`): whether the project is complete,
  * and where a change belongs.
  */
class ReportsSuite extends munit.CatsEffectSuite:
  test("complete: every node accepted and proven") {
    for
      trusted <- Opened.api(Opened.trusted)
      _       <- Opened.acceptAll(trusted)
      done    <- trusted.reading.view
      lone    <- Opened.api(Opened.lone)
      _       <- Opened.acceptAll(lone)
      leaf    <- lone.reading.view
      fresh   <- Opened.api(Opened.trusted).flatMap(_.reading.view)
    yield
      assert(done.overview.complete, done.nodes.map(n => (n.id, n.review.standing, n.proof.unproven)))
      // A leaf nothing below proves is not; nor is a project whose nodes are not accepted yet.
      assert(!leaf.overview.complete)
      assert(!fresh.overview.complete)
  }

  test("a leaf its code is tested against is not one nothing below proves") {
    for
      api  <- Opened.api(Opened.before)
      _    <- Opened.acceptAll(api)
      done <- api.reading.view
    yield
      val unproven = done.nodes.map(n => n.id -> n.proof.unproven).toMap
      assert(!unproven.getOrElse(id("sameAbove"), Nil).contains(Unproven.NothingBelow), unproven)
  }

  test("find: the nodes governing a file, a file no node governs, or what mentions every word") {
    val shelf = RelPath.fromIdentifiers("src/main", "shelf/Shelf.scala")
    for
      ports <- Opened.ports(Map(shelf -> "object Shelf"))
      api   <- Opened.over(Opened.project(Shelf.Governed.kb), ports)
      found <- List("./src/main/shelf/Shelf.scala", "src/main/", "src/Other.scala", "service NUMBER itself", "dragons")
                 .traverse(api.reading.find)
    yield
      val design = List(id("inShelf"))
      assertEquals(found, List(Found(Nil, design), Found(Nil, design), Found(Nil, Nil),
        Found(List(id("sameAbove")), Nil), Found(Nil, Nil)))
  }

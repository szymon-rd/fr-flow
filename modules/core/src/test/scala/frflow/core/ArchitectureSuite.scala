package frflow.core

import frflow.core.expr.Quantifier
import frflow.core.spec.{NodeKind, Statement}
import frflow.core.vocab.ValueKind
import java.nio.file.{Files, Path}
import scala.compiletime.constValueTuple
import scala.deriving.Mirror
import scala.jdk.CollectionConverters.*

/** The rules that keep the modules apart (ARCHITECTURE.md, section 11, rules 2 and 9), read off every module's
  * sources and `project/architecture.conf`: what a module names of another, package cycles, `private[frflow]`,
  * `ThreadLocal`, effects and IO in the pure modules, locks outside the places that take them, and the owner's
  * concepts (§15).
  */
class ArchitectureSuite extends munit.FunSuite:
  private val root: Path = LazyList.iterate(Path.of("").toAbsolutePath)(_.getParent).takeWhile(_ != null)
    .find(d => Files.isRegularFile(d.resolve("project/architecture.conf"))).getOrElse(fail("no architecture.conf"))
  private val conf = Files.readAllLines(root.resolve("project/architecture.conf")).asScala.toList.map(_.trim)
    .filterNot(l => l.isEmpty || l.startsWith("#"))
  private val sources = Sources(root.resolve("modules"))
  private def listed(word: String): List[String] = conf.filter(_.startsWith(word + " ")).map(_.drop(word.length + 1))
  private def arrows(lines: List[String]): Map[String, List[String]] = lines.map(_.split("->").map(_.trim)).map(a =>
    a(0) -> a(1).split(",").map(_.trim).toList).groupMapReduce(_._1)(_._2)(_ ++ _)
  private val edges = arrows(conf.filter(l => l.contains("->") && !l.startsWith("tests ")))
  private val testEdges = arrows(listed("tests"))
  private val pure = Set("core", "dsl", "proof", "decision")

  test("every module's main sources name of another module only what architecture.conf lists") {
    val named = sources.main.flatMap(f => f.refs.filter(r => r.module != f.module).filterNot(r =>
      edges.getOrElse(f.module, Nil).exists(e => r.within(e))).map(r => s"${f.rel}: ${r.path}"))
    assert(sources.main.size > 500, sources.main.size)
    assertEquals(named.distinct, Nil)
  }

  test("every module's test sources name only what its main may, transitively, and its test-only edges") {
    def reach(m: String, seen: Set[String]): Set[String] =
      (edges.getOrElse(m, Nil).map(_.takeWhile(_ != '.')) ++ testEdges.getOrElse(m, Nil)).toSet.diff(seen)
        .foldLeft(seen + m)((s, n) => reach(n, s))
    val modules = sources.main.map(_.module).toSet
    // A test's own package under `frflow` (eval's `frflow.vocab`) is no module's.
    val named = sources.tests.flatMap(f => f.refs.filter(r => modules(r.module))
      .filterNot(r => reach(f.module, Set.empty)(r.module))
      .map(r => s"${f.rel}: ${r.path}"))
    assertEquals(named.distinct, Nil)
  }

  test("the package cycles inside a module are the ones listed, and no other") {
    val found = sources.main.groupBy(_.module).values.toList.flatMap(Cycles.of).map(_.sorted).toSet
    val kept = listed("cycle").map(_.split(",").map(p => s"frflow.${p.trim}").toList.sorted).toSet
    assertEquals(found.diff(kept), Set.empty, "a new cycle")
    assertEquals(kept.diff(found), Set.empty, "a cycle listed that is gone: drop it from architecture.conf")
  }

  test("no private[frflow], and no ThreadLocal") {
    val bad = (sources.main ++ sources.tests).filter(f => f.code.contains("private[frflow]") ||
      f.code.contains("ThreadLocal")).map(_.rel)
    assertEquals(bad, Nil)
  }

  test("no effects, JSON, files, randomness or environment in core, dsl, proof or decision, but a macro's") {
    val Banned =
      """cats\.effect|io\.circe|java\.nio\.file\.(Files|\{[^}]*\bFiles\b)|scala\.util\.Random|System\.getenv""".r
    val io = listed("io").toSet
    val bad = sources.main.filter(f => pure(f.module) && !io(f.name)).flatMap(f =>
      Banned.findFirstIn(f.code).map(m => s"${f.rel}: $m"))
    assertEquals(bad, Nil)
  }

  test("locks only where architecture.conf says one is taken") {
    val Lock = """\bMutex\b|\bsynchronized\b|java\.util\.concurrent\.atomic""".r
    val places = listed("lock").toSet
    val bad = sources.main.filterNot(f => places(f.name))
      .flatMap(f => Lock.findFirstIn(f.code).map(m => s"${f.rel}: $m"))
    assertEquals(bad, Nil)
    assertEquals(places.diff(sources.main.filter(f => Lock.findFirstIn(f.code).isDefined).map(_.name).toSet), Set.empty)
  }

  test("the owner's concepts stay the only ones (§15): three kinds of node, two of value, two quantifiers") {
    assertEquals(cases[Statement], List("Claim", "Assumption", "Design"))
    assertEquals(NodeKind.values.toList.map(_.toString), List("Claim", "Assumption", "Design"))
    assertEquals(ValueKind.values.toList.map(_.toString), List("Declaration", "Definition"))
    // The IR's: `forall` and `always`, and the term algebra's `Exists`, which no form of the facade writes.
    assertEquals(Quantifier.values.toList.map(_.toString), List("Forall", "Exists", "Always"))
    val facade = sources.main.find(_.rel.endsWith("eval/src/main/scala/frflow/package.scala"))
      .getOrElse(fail("no facade")).code
    assert(!facade.contains("Terms") && !"""\bexists\b""".r.findFirstIn(facade).isDefined, facade)
  }

  test("the scan reads a path, names in braces and the facade; not a comment or a string") {
    def named(text: String) = Source.Named.findAllMatchIn(Source.code(text)).map(_.matched).toList
    assertEquals(named("import frflow.core.spec.{NodeKind, Statement}"), List("frflow.core.spec"))
    assertEquals(named("import frflow.{api as a, Node}\nimport frflow.*"), List("frflow.{api as a, Node}", "frflow.*"))
    assertEquals(named("// frflow.project\n/* frflow.wire */ val s = \"frflow.proof\""), Nil)
    assert(Ref("frflow.core.spec.x").within("core.spec") && Ref("frflow.core.spec").within("core"))
    assert(!Ref("frflow.core.specs").within("core.spec") && Ref("frflow").within("eval"))
  }

  private inline def cases[T](using m: Mirror.SumOf[T]): List[String] =
    constValueTuple[m.MirroredElemLabels].toList.map(_.toString)

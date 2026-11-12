package frflow.core

import frflow.core.expr.Quantifier
import frflow.core.spec.{NodeKind, Statement}
import frflow.core.vocab.ValueKind
import java.nio.file.{Files, Path}
import scala.compiletime.constValueTuple
import scala.deriving.Mirror
import scala.jdk.CollectionConverters.*

/** The rules that keep the modules apart (ARCHITECTURE.md, section 11, rules 2 and 9), read off every module's
  * sources and `project/architecture.conf`: what a module names of another, what an example names of FrFlow (only
  * the facade, and an app the front ends' entry points), package cycles, one package clause a
  * file, `private[frflow]`, `ThreadLocal`, effects, IO, randomness and the environment in the pure modules, locks
  * outside the places that take them, and the owner's concepts (§15). The conf's exceptions are counted here, so a
  * new one is a change to this suite as well as to the conf.
  */
class ArchitectureSuite extends munit.FunSuite:
  private val root: Path = LazyList.iterate(Path.of("").toAbsolutePath)(_.getParent).takeWhile(_ != null)
    .find(d => Files.isRegularFile(d.resolve("project/architecture.conf"))).getOrElse(fail("no architecture.conf"))
  private val conf = Files.readAllLines(root.resolve("project/architecture.conf")).asScala.toList.map(_.trim)
    .filterNot(l => l.isEmpty || l.startsWith("#"))
  private val sources = Sources.of(root, "modules")
  private val examples = Sources.of(root, "examples").all
  private def listed(word: String): List[String] = conf.filter(_.startsWith(word + " ")).map(_.drop(word.length + 1))
  private def arrows(lines: List[String]): Map[String, List[String]] = lines.map(_.split("->").map(_.trim)).map(a =>
    a(0) -> a(1).split(",").map(_.trim).toList).groupMapReduce(_._1)(_._2)(_ ++ _)
  private val edges =
    arrows(conf.filter(l => l.contains("->") && !l.startsWith("tests ") && !l.startsWith("example ")))
  private val testEdges = arrows(listed("tests"))
  private val pure = Set("core", "dsl", "proof", "decision")

  test("every module's main sources name of another module only what architecture.conf lists") {
    assert(sources.main.size > 500, sources.main.size)
    assertEquals(Architecture.crossing(sources.main, edges), Nil)
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

  test("an example's model names of FrFlow only the facade, and its app the front ends' entry points too") {
    assert(examples.size > 30, examples.size)
    assertEquals(Architecture.outsideFacade(examples, arrows(listed("example"))), Nil)
  }

  test("the package cycles inside a module are the ones listed, and no other") {
    val found = sources.main.groupBy(_.module).values.toList.flatMap(Cycles.of).map(_.sorted).toSet
    val kept = listed("cycle").map(_.split(",").map(p => s"frflow.${p.trim}").toList.sorted).toSet
    assertEquals(found.diff(kept), Set.empty, "a new cycle")
    assertEquals(kept.diff(found), Set.empty, "a cycle listed that is gone: drop it from architecture.conf")
  }

  test("one package clause a file, no private[frflow], and no ThreadLocal, in the modules and the examples") {
    val bad = (sources.all ++ examples).filter(f => f.clauses.size > 1 || f.code.contains("private[frflow]") ||
      f.code.contains("ThreadLocal")).map(_.rel)
    assertEquals(bad, Nil)
  }

  test("no effects, JSON, files, randomness or environment in core, dsl, proof or decision, but a macro's") {
    val io = listed("io").toSet
    assertEquals(sources.main.filter(f => pure(f.module) && !io(f.name)).flatMap(Architecture.impure), Nil)
  }

  test("locks only where architecture.conf says one is taken") {
    val places = listed("lock").toSet
    assertEquals(sources.main.filterNot(f => places(f.name)).flatMap(Architecture.locks), Nil)
    assertEquals(places.diff(sources.main.filter(f => Architecture.locks(f).nonEmpty).map(_.name).toSet), Set.empty)
  }

  test("the exceptions architecture.conf lists are these many: a new one changes this suite too") {
    assertEquals((listed("cycle").size, listed("lock").size, listed("io").size), (2, 3, 2))
  }

  test("the owner's concepts stay the only ones (§15): three kinds of node, two of value, two quantifiers") {
    assertEquals(cases[Statement], List("Claim", "Assumption", "Design"))
    assertEquals(NodeKind.values.toList.map(_.toString), List("Claim", "Assumption", "Design"))
    assertEquals(ValueKind.values.toList.map(_.toString), List("Declaration", "Definition"))
    // The IR's: `forall` and `always`, and the term algebra's `Exists`, which no form of the facade writes: rooms'
    // `FormsSuite` (testing's tests) checks that `exists` over a type does not compile with `import frflow.*`.
    assertEquals(Quantifier.values.toList.map(_.toString), List("Forall", "Exists", "Always"))
  }

  private inline def cases[T](using m: Mirror.SumOf[T]): List[String] =
    constValueTuple[m.MirroredElemLabels].toList.map(_.toString)

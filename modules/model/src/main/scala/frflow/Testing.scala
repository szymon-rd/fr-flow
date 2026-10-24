package frflow

import frflow.protocol.NodeKind
import java.util.SplittableRandom
import scala.annotation.tailrec
import scala.collection.mutable
import scala.util.{Failure, Success, Try}

/** A generator a developer or an agent gives for a type the derived one serves badly: `Gen.oneOf(Path("/a"), Path("/b"))`.
  * It is typed, so its values are of the type. What it says it makes is shown beside the results, and the derived
  * generator keeps making a share of the type's values, so a narrow generator never hides the rest.
  */
/** How many cases a contract's code is tested on, and from which seed: the same seed, the same cases. */
final case class TestSettings(cases: Int = 1000, seed: Long = 1)

object TestSettings:
  /** `settings`, with the seed `check` is given (`FRFLOW_SEED`): a number, or `fresh` (a new one for the run, shown in
    * the report). CI runs the fixed seed, then a fresh one: what the fixed one keeps passing, a fresh one may still find.
    */
  def inForce(settings: TestSettings, seed: Option[String]): TestSettings = seed.map(_.trim) match
    case Some("fresh")                           => settings.copy(seed = fresh)
    case Some(s) if s.toLongOption.isDefined      => settings.copy(seed = s.toLong)
    case _                                       => settings
  /** One fresh seed per run: what a result's key and the run itself agree on. */
  private lazy val fresh: Long = System.nanoTime

final class Gen[A] private[frflow] (val describe: String, private[frflow] val draw: Draw => A):
  def map[B](f: A => B): Gen[B] = Gen(describe, d => f(draw(d)))
  def flatMap[B](f: A => Gen[B]): Gen[B] = Gen(describe, d => f(draw(d)).draw(d))
  /** What the generator makes, in the developer's words. */
  def describedAs(text: String): Gen[A] = Gen(text, draw)

object Gen:
  def oneOf[A](first: A, rest: A*): Gen[A] =
    val all = (first +: rest).toVector
    Gen(s"one of ${all.map(Example.show).mkString(", ")}", d => all(d.below(all.size)))
  def choose(lo: Int, hi: Int): Gen[Int] = Gen(s"from $lo to $hi", d => lo + d.below(hi - lo + 1))
  def chooseBig(lo: BigInt, hi: BigInt): Gen[BigInt] =
    Gen(s"from $lo to $hi", d => lo + BigInt(d.below((hi - lo + 1).min(BigInt(Int.MaxValue)).toInt)))
  def listOf[A](g: Gen[A]): Gen[List[A]] = Gen(s"lists of ${g.describe}", d => List.fill(d.length)(g.draw(d)))
  def const[A](a: A): Gen[A] = Gen(Example.show(a), _ => a)
  /** What FrFlow derives from the type. */
  def derived[A](using t: LeanType[A]): Gen[A] = Gen("derived from the type", d => d.value(t).asInstanceOf[A])

/** A function a test made up: a table of answers, and its answer elsewhere. What a function-typed parameter
  * (`sessions: String => Option[UserId]`) is generated as.
  */
sealed trait Table:
  def entries: List[(List[Any], Any)]
  def default: Any
  protected def at(args: List[Any]): Any = entries.find(_._1 == args).fold(default)(_._2)
  def shown: String =
    val es = entries.map((k, v) => s"${k.map(Example.show).mkString(", ")} ↦ ${Example.show(v)}")
    (es :+ s"else ${Example.show(default)}").mkString("{", ", ", "}")
private[frflow] final case class Table1(entries: List[(List[Any], Any)], default: Any) extends Table with (Any => Any):
  def apply(a: Any): Any = at(List(a))
  override def toString: String = shown
private[frflow] final case class Table2(entries: List[(List[Any], Any)], default: Any) extends Table with ((Any, Any) => Any):
  def apply(a: Any, b: Any): Any = at(List(a, b))
  override def toString: String = shown
private[frflow] final case class Table3(entries: List[(List[Any], Any)], default: Any) extends Table with ((Any, Any, Any) => Any):
  def apply(a: Any, b: Any, c: Any): Any = at(List(a, b, c))
  override def toString: String = shown
private[frflow] object Table:
  def apply(arity: Int, entries: List[(List[Any], Any)], default: Any): Table = arity match
    case 1 => Table1(entries, default)
    case 2 => Table2(entries, default)
    case 3 => Table3(entries, default)
    case n => throw CannotGenerate(s"a function of $n arguments")

private[frflow] final class CannotGenerate(what: String) extends RuntimeException(s"cannot generate $what")

/** What a contract's cases are made of: the generators given for some types, the examples' values (seeds, by type),
  * their numbers, and the types the definitions in force give the opaque terms. For an outside system's code (an
  * assumption's: a database), a given generator says what the outside can hold, and is all that type is drawn from,
  * with the examples' values: data it cannot hold (two rows with one key) is no finding.
  */
private[frflow] final class Plan(custom: Map[String, Gen[?]], seeds: Map[String, Vector[Any]], val numbers: List[BigInt],
    opaques: Map[String, LeanType[?]], outside: Boolean = false):
  private val keys = new java.util.IdentityHashMap[LeanType[?], String]()
  /** A type's name, as Scala tells its values apart (an Int is not a Long, though Lean names both `Int`). */
  def key(t: LeanType[?]): String =
    Option(keys.get(t)).getOrElse { val k = Plan.name(t); keys.put(t, k); k }
  def customFor(t: LeanType[?]): Option[Gen[?]] = custom.get(key(t))
  /** Only the given generator and the examples make this type's values. */
  def only(t: LeanType[?]): Boolean = outside && custom.contains(key(t))
  /** The type holds, at some depth, values only a given generator makes: a value near one of its seeds (a list's
    * element repeated, a field changed) may be one the outside cannot hold, so none is made.
    */
  def holdsOnly(t: LeanType[?]): Boolean =
    def go(u: LeanType[?], seen: Set[String]): Boolean =
      val k = key(u)
      only(u) || !seen(k) && (u.shape match
        case Shape.ListOf(a)   => go(a, seen + k)
        case Shape.OptionOf(a) => go(a, seen + k)
        case Shape.SetOf(a)    => go(a, seen + k)
        case Shape.MapOf(x, y) => go(x, seen + k) || go(y, seen + k)
        case Shape.TupleOf(as) => as.exists(go(_, seen + k))
        case Shape.FnOf(as, r) => (as :+ r).exists(go(_, seen + k))
        case Shape.Data(adt)   => adt.ctors.exists(_.fields.exists((_, f) => go(f, seen + k)))
        case Shape.Opq(o)      => opaques.get(o.name).exists(go(_, seen + k))
        case _                 => false)
    outside && custom.nonEmpty && go(t, Set.empty)
  def seedsOf(t: LeanType[?]): Vector[Any] = seeds.getOrElse(key(t), Vector.empty)
  def opaque(o: Opaque): Option[LeanType[?]] = opaques.get(o.name)

private[frflow] object Plan:
  def name(t: LeanType[?]): String = t.shape match
    case Shape.Num(k)      => k.toString
    case Shape.Data(a)     => a.name
    case Shape.Opq(o)      => s"${o.name}.T"
    case Shape.ListOf(a)   => s"List[${name(a)}]"
    case Shape.OptionOf(a) => s"Option[${name(a)}]"
    case Shape.SetOf(a)    => s"Set[${name(a)}]"
    case Shape.MapOf(k, v) => s"Map[${name(k)}, ${name(v)}]"
    case Shape.TupleOf(as) => as.map(name).mkString("(", ", ", ")")
    case Shape.FnOf(as, r) => (as :+ r).map(name).mkString("(", " => ", ")")
    case other             => other.toString

  /** The values a value holds, by type: a grant table gives grants, users and paths. */
  def harvest(t: LeanType[?], v: Any, opaques: Map[String, LeanType[?]], key: LeanType[?] => String,
      into: mutable.Map[String, Vector[Any]]): Unit =
    def add(x: Any) = into.updateWith(key(t))(s => Some(s.fold(Vector(x))(xs => if xs.contains(x) || xs.size >= 12 then xs else xs :+ x)))
    def go(u: LeanType[?], x: Any) = harvest(u, x, opaques, key, into)
    (t.shape, v) match
      case (Shape.ListOf(a), xs: List[?])     => add(v); xs.foreach(go(a, _))
      case (Shape.OptionOf(a), Some(x))       => add(v); go(a, x)
      case (Shape.SetOf(a), xs: Set[?])       => add(v); xs.foreach(go(a, _))
      case (Shape.MapOf(k, w), m: Map[?, ?])  => add(v); m.foreach((x, y) => { go(k, x); go(w, y) })
      case (Shape.TupleOf(as), p: Product)    => add(v); as.zip(p.productIterator.toList).foreach(go(_, _))
      case (Shape.Data(adt), p)               => add(v); adt.ctorOf(p).fields.zip(fields(p)).foreach { case ((_, f), x) => go(f, x) }
      case (Shape.Opq(o), x)                  => add(v); opaques.get(o.name).foreach(go(_, x))
      case (Shape.FnOf(as, r), t: Table)      => add(v); t.entries.foreach((ks, x) => { as.zip(ks).foreach(go(_, _)); go(r, x) })
      case (Shape.FnOf(_, _), _) | (Shape.Unknown, _) => ()
      case _                                  => add(v)
  private def fields(v: Any): List[Any] = v match
    case p: Product => p.productIterator.toList
    case _          => Nil

/** One generated case: its random numbers, its size, and the values it has made of each type, so that the token a
  * table holds and the token asked about are often the same.
  */
final class Draw private[frflow] (rnd: SplittableRandom, val size: Int, plan: Plan):
  private val pools = mutable.Map.empty[String, mutable.ArrayBuffer[Any]]
  private var depth = 0
  def below(n: Int): Int = if n <= 1 then 0 else rnd.nextInt(n)
  def chance(p: Double): Boolean = rnd.nextDouble() < p
  /** How many elements a list gets: fewer the deeper it is. */
  def length: Int = below(size / (depth + 1) + 2)

  private[frflow] def value(t: LeanType[?]): Any =
    val seeds = plan.seedsOf(t)
    plan.customFor(t) match
      case Some(g) if chance(0.75) || plan.only(t) && (seeds.isEmpty || chance(0.8)) => g.draw(this)
      case Some(_) if plan.only(t) => seeds(below(seeds.size))
      case _ =>
        val k = plan.key(t)
        lazy val pool = pools.getOrElseUpdate(k, mutable.ArrayBuffer.empty)
        if seeds.nonEmpty && chance(0.15) then seeds(below(seeds.size))
        else if seeds.nonEmpty && chance(0.1) then
          val s = seeds(below(seeds.size))
          (if plan.holdsOnly(t) then Nil else Probes.near(s, plan.numbers)) match
            case Nil  => s
            case near => near(below(near.size))
        else if pooled(t) && pool.nonEmpty && chance(0.6) then pool(below(pool.size))
        else
          val v = fresh(t)
          if pooled(t) && pool.size < 4 then pool += v
          v

  private def pooled(t: LeanType[?]): Boolean = t.shape match
    case Shape.Str | Shape.Num(_) | Shape.Opq(_) | Shape.Data(_) => true
    case _ => false

  private def nested[A](f: => A): A =
    depth += 1
    try f
    finally depth -= 1

  private def number: BigInt =
    if chance(0.3) then BigInt(below(3) - 1)
    else if plan.numbers.nonEmpty && chance(0.4) then plan.numbers(below(plan.numbers.size)) + (below(3) - 1)
    else BigInt(below(20 * size + 1) - 10 * size)

  private def string: String =
    if chance(0.2) then "" else List.fill(below(4) + 1)("ab1"(below(3))).mkString

  private def default(r: LeanType[?]): Any = r.shape match
    case Shape.OptionOf(_) => None
    case Shape.Prop        => false
    case Shape.ListOf(_)   => Nil
    case _                 => value(r)

  private def fresh(t: LeanType[?]): Any = t.shape match
    case Shape.Prop        => chance(0.5)
    case Shape.Num(k)      => k.of(number)
    case Shape.Str         => string
    case Shape.UnitT       => ()
    case Shape.ListOf(a)   => nested(List.fill(length)(value(a)))
    case Shape.OptionOf(a) => if chance(0.25) then None else Some(nested(value(a)))
    case Shape.MapOf(k, v) => nested(List.fill(length)(value(k) -> value(v)).toMap)
    case Shape.SetOf(a)    => nested(List.fill(length)(value(a)).toSet)
    case Shape.TupleOf(as) => Tuple.fromArray(as.map(value(_).asInstanceOf[Object]).toArray)
    case Shape.FnOf(as, r) => nested(Table(as.size, List.fill(length)(as.map(value) -> value(r)), default(r)))
    case Shape.Opq(o)      => value(plan.opaque(o).getOrElse(throw CannotGenerate(s"${o.name}: no definition fixes it")))
    case Shape.Data(adt)   =>
      // Deep down, a case with no fields: the value stays small.
      val cs = if depth > 2 && adt.ctors.exists(_.fields.isEmpty) then adt.ctors.filter(_.fields.isEmpty) else adt.ctors
      val c = cs(below(cs.size))
      c.singleton.getOrElse(nested(c.make(c.fields.map((_, f) => value(f)))))
    case _                 => throw CannotGenerate(Types.scala(t))

/** Smaller values of a type, the smallest first: what a failing case is shrunk with. A value of a `fixed` type (one only
  * a given generator makes: what the outside can hold) is never shrunk, at any depth: a smaller one may be one the
  * outside cannot hold.
  */
private[frflow] object Shrink:
  def of(t: LeanType[?], v: Any, opaques: Map[String, LeanType[?]], fixed: LeanType[?] => Boolean = _ => false): LazyList[Any] =
    if fixed(t) then LazyList.empty else ofType(t, v, opaques, fixed)

  private def ofType(t: LeanType[?], v: Any, opaques: Map[String, LeanType[?]], fixed: LeanType[?] => Boolean): LazyList[Any] =
    def go(u: LeanType[?], x: Any) = of(u, x, opaques, fixed)
    def list(a: LeanType[?], xs: List[Any]): LazyList[List[Any]] =
      if xs.isEmpty then LazyList.empty
      else (Nil #:: xs.take(xs.size / 2) #:: LazyList.from(xs.indices).map(i => xs.patch(i, Nil, 1))) ++
        LazyList.from(xs.indices).flatMap(i => go(a, xs(i)).take(4).map(y => xs.updated(i, y)))
    (t.shape, v) match
      case (Shape.Prop, true)                => LazyList(false)
      case (Shape.Num(k), x)                 =>
        val n = x match { case i: Int => BigInt(i); case l: Long => BigInt(l); case b: BigInt => b; case _ => BigInt(0) }
        if n == 0 then LazyList.empty else LazyList(BigInt(0), n / 2, n - n.signum).distinct.filter(_ != n).map(k.of)
      case (Shape.Str, s: String)            =>
        if s.isEmpty then LazyList.empty else LazyList("", s.take(s.length / 2), s.dropRight(1)).distinct.filter(_ != s)
      case (Shape.ListOf(a), xs: List[?])    => list(a, xs)
      case (Shape.SetOf(a), xs: Set[?])      => list(a, xs.toList).map(_.toSet)
      case (Shape.MapOf(k, w), m: Map[?, ?]) => list(LeanType.of[Any](Shape.TupleOf(List(k, w))), m.toList).map(_.asInstanceOf[List[(Any, Any)]].toMap)
      case (Shape.OptionOf(a), Some(x))      => None #:: go(a, x).map(Some(_))
      case (Shape.TupleOf(as), p: Product)   =>
        val xs = p.productIterator.toList
        LazyList.from(xs.indices).flatMap(i => go(as(i), xs(i)).map(y => Tuple.fromArray(xs.updated(i, y).map(_.asInstanceOf[Object]).toArray)))
      case (Shape.FnOf(as, _), tb: Table)    =>
        if tb.entries.isEmpty then LazyList.empty
        else Table(as.size, Nil, tb.default) #:: LazyList.from(tb.entries.indices).map(i => Table(as.size, tb.entries.patch(i, Nil, 1), tb.default))
      case (Shape.Opq(o), x)                 => opaques.get(o.name).fold(LazyList.empty)(go(_, x))
      case (Shape.Data(adt), x)              =>
        val c = adt.ctorOf(x)
        // A case with no fields, earlier in the enum, is simpler; then each field smaller.
        val simpler = if adt.isEnum then adt.ctors.takeWhile(_ ne c).flatMap(_.singleton).to(LazyList) else LazyList.empty
        val fs = x.asInstanceOf[Product].productIterator.toList
        simpler ++ (if c.fields.isEmpty then LazyList.empty
          else LazyList.from(fs.indices).flatMap(i => go(c.fields(i)._2, fs(i)).map(y => c.make(fs.updated(i, y)))))
      case _ => LazyList.empty

/** Testing a contract's code against the contract: the property is the contract's own formula, run in Scala on cases
  * generated from the types (the examples' values among them), on the code's result; the formula's parts are counted,
  * so a part no case reaches is said, not passed.
  */
private[frflow] object Testing:
  /** A failing case, shrunk: shown, why it fails, and where it came from (the same seed, index and size make it again). */
  final case class Failed(shown: String, why: String, seed: Long, index: Int, size: Int)
  /** A case to try first: one that failed before. */
  final case class Replay(seed: Long, index: Int, size: Int)
  final case class Covered(part: String, held: Int)
  /** `against`: what the code is tested against (the contract, or the proven define it runs beside). */
  final case class Report(cases: Int, seed: Long, against: String, failure: Option[Failed], coverage: List[Covered], notes: List[String]):
    def passed: Boolean = failure.isEmpty && coverage.forall(_.held > 0)

  /** The code of a contract that is tested, not proven: plain code on its operation, or code run beside a proven define. */
  def testable(kb: KnowledgeBase, n: Node[?]): Option[Implementation] =
    kb.implementation(n).filter(i => !i.flow && !i.provenCode && !n.isFlow && n.post.isDefined && n.op.isDefined)

  /** Whether the node has code tested by `run`: a contract's plain code, or implementations of a boundary's model. */
  def tests(kb: KnowledgeBase, n: Node[?]): Boolean = testable(kb, n).isDefined || ModelTests.testable(n)

  def run(kb: KnowledgeBase, n: Node[?], settings: TestSettings, replay: List[Replay] = Nil): Option[Report] =
    if ModelTests.testable(n) then Some(ModelTests.run(kb, n, settings, replay))
    else testable(kb, n).map(i => Run(kb, n, i).report(settings, replay))

  /** The types the definitions in force give the opaque terms: what an opaque value is generated as. */
  def opaques(kb: KnowledgeBase): Map[String, LeanType[?]] =
    kb.opaques.flatMap(o => kb.provisional.get(o.name).flatMap(_.substs.find(_.name == o.name)).flatMap(_.typeOf).map(o.name -> _)).toMap

  /** The size a case is made at: small first, larger later. */
  def sizeOf(i: Int, cases: Int): Int = 1 + i * 10 / cases.max(1)
  private[frflow] def random(seed: Long, i: Int): SplittableRandom = SplittableRandom(seed * 0x9E3779B97F4A7C15L + i)

  private final class Run(kb: KnowledgeBase, n: Node[?], impl: Implementation):
    private val untyped = n.asInstanceOf[Node[(Any, Any) => Any]]
    private val (ta, tb, tr) = n.op.get.termType.shape match
      case Shape.FnOf(List(a, b), r) => (a, b, r)
      case other => throw IllegalArgumentException(s"FrFlow: ${n.id}'s operation takes two arguments")
    private val post = untyped.postFn.get
    private val reference = impl.proven.map(d => (d.name, d.lifted.value.asInstanceOf[(Any, Any) => Any]))
    private val against = reference.fold(n.id)((name, _) => s"the proven define $name, and ${n.id}")

    // The world: what the formula reads (through the definitions in force) and the examples bind, less the operations.
    // (A parameter only plain code reads, a database handle, the model does not know: the examples bind it.)
    private val read = (n.post.toList ++ n.kept.flatMap(k => k.view.toList ++ k.invariant.rule.toList)).flatMap(kb.reads)
    private def defined(p: Param[?]) = kb.provisional.get(p.name).exists(_.substs.exists(s => s.name == p.name && s.term.isDefined))
    private val params = (read.flatMap(r => kb.params.find(_.name == r)) ++ n.cases.flatMap(_.bindings.map(_.param)))
      .distinctBy(_.name).filterNot(p => kb.isOp(p.name) || defined(p))
    private val (generated, fixedParams) = params.partition(p => known(p.termType))
    private val fixed: List[Binding] = fixedParams.flatMap(p => n.cases.flatMap(_.bindings).find(_.param.name == p.name))
    private val types: Vector[LeanType[?]] = (generated.map(_.termType) ++ List(ta, tb)).toVector

    private val opaques: Map[String, LeanType[?]] = Testing.opaques(kb)
    private val customs: Map[LeanType[?], Gen[?]] = kb.generators.toMap
    private val plan =
      val keyOf = Plan(Map.empty, Map.empty, Nil, opaques)
      val seeds = mutable.LinkedHashMap.empty[String, Vector[Any]]
      def harvest(t: LeanType[?], v: Any) = Plan.harvest(t, v, opaques, keyOf.key, seeds)
      n.cases.foreach { e =>
        Try { harvest(ta, e.a); harvest(tb, e.b); harvest(tr, e.result) }
        generated.flatMap(p => e.bindings.find(_.param.name == p.name).map(b => p -> b)).foreach { (p, b) =>
          Try(Bindings.within(e.bindings)(harvest(p.termType, b.table.fold(b.value())(t => Table(1, t.toList.map((k, v) => (List(k), Some(v))), None)))))
        }
      }
      Plan(customs.map((t, g) => keyOf.key(t) -> g), seeds.toMap, Probes.boundaries(n.cases).flatMap(x => List(x - 1, x, x + 1)).distinct,
        opaques, outside = n.kind == NodeKind.Assumption)

    private def known(t: LeanType[?]): Boolean = t.shape match
      case Shape.Unknown | Shape.WorldT | Shape.FlowOf(_) => false
      case Shape.ListOf(a)   => known(a)
      case Shape.OptionOf(a) => known(a)
      case Shape.SetOf(a)    => known(a)
      case Shape.MapOf(k, v) => known(k) && known(v)
      case Shape.TupleOf(as) => as.forall(known)
      case Shape.FnOf(as, r) => as.size <= 3 && (as :+ r).forall(known)
      case Shape.Opq(o)      => opaques.contains(o.name)
      case _                 => true

    // The parts of the formula a test must reach: an implication's premise, each side of an or, each branch, each case
    // of a match, and each list or option a `forall`/`exists` ranges over, not empty.
    private val printer = LeanPrinter()
    private val formula = n.post.get.built
    printer.print(formula._1, formula._2.termTree, formula._2.termType)
    private val targets: List[(Tree, Int, String)] =
      Coverage.targets(formula._2.termTree, t => Try(printer.expr(t)).getOrElse("…"))

    /** Counts the parts reached; ranges a quantifier over values made for its types (sampled: said in the report). */
    private final class Counter(draw: () => Draw) extends Watch:
      val hits = new java.util.IdentityHashMap[Tree, mutable.Map[Int, Int]]()
      var sampled = Set.empty[String]
      targets.foreach((t, _, _) => hits.putIfAbsent(t, mutable.Map.empty))
      def hit(t: Tree, outcome: Int): Unit = Option(hits.get(t)).foreach(m => m.update(outcome, m.getOrElse(outcome, 0) + 1))
      def range(ts: List[LeanType[?]]): Option[List[List[Any]]] = Try {
        sampled ++= ts.map(Types.scala)
        val d = draw()
        val each = ts.map(t => (plan.seedsOf(t).take(3) ++ List.fill(5)(d.value(t))).distinct.toList)
        each.foldRight(List(List.empty[Any]))((xs, rows) => for x <- xs; r <- rows yield x :: r)
      }.toOption
      def held(t: Tree, outcome: Int): Int = Option(hits.get(t)).flatMap(_.get(outcome)).getOrElse(0)

    /** A case: its values (the world's, then the two arguments), what the code returned, and why it fails, if it does. */
    private def attempt(vals: Vector[Any], watch: Option[Watch]): (Option[Any], Option[String]) =
      on(generated.zip(vals).map((p, v) => Binding(p, () => v)), vals(generated.size), vals(generated.size + 1), watch)

    // The operations the code was seen to call: plain code says which it calls (`implement(c, op)`), and is held to it.
    private val calledOps = mutable.Set.empty[String]
    private val named = impl.calls.toSet ++ n.op.map(_.name) ++
      kb.onOp.keySet.filter(o => s"\\b${java.util.regex.Pattern.quote(o)}\\b".r.findFirstIn(impl.wiring).isDefined)

    private def on(world: List[Binding], a: Any, b: Any, watch: Option[Watch]): (Option[Any], Option[String]) =
      Bindings.within(kb.opCode ++ kb.definitionBindings ++ fixed ++ world) {
        Try(Bindings.reading(impl.factory().asInstanceOf[(Any, Any) => Any](a, b))) match
          case Failure(e) => (None, Some(s"error: ${Option(e.getMessage).getOrElse(e.toString)}"))
          case Success((r, read)) =>
            calledOps ++= read.filter(kb.isOp)
            def onContract = Try(watch.fold(post(a, b, r))(Watch.within(_)(post(a, b, r)))) match
              case Success(true)  => None
              case Success(false) => Some(s"returned ${Example.show(r)}, which ${n.id} refuses")
              case Failure(e: NotExecutable) => Some(s"${n.id} cannot be run here: ${e.getMessage}")
              case Failure(e)     => Some(s"${n.id} could not be evaluated: ${Option(e.getMessage).getOrElse(e.toString)}")
            val unlike = reference.flatMap((name, f) => Try(f(a, b)).toOption.filterNot(same(_, r))
              .map(x => s"returned ${Example.show(r)}, where the proven define $name returns ${Example.show(x)}"))
            (Some(r), unlike.orElse(onContract).orElse(untyped.broken(a, b, r).map(i => s"returned ${Example.show(r)}, which breaks the invariant $i")))
      }

    // A list the outside returns in its own order is the same result in another order.
    private def same(x: Any, y: Any): Boolean = (x, y) match
      case (xs: List[?], ys: List[?]) => xs.size == ys.size && xs.diff(ys).isEmpty
      case _ => x == y

    // Each example as a whole case (its world and its call): a third of the cases start from one, with one value changed,
    // so what holds only when the world's parts agree (a user signed in, then disabled) is reached.
    private val exampleCases: Vector[Vector[Option[Any]]] = n.cases.toVector.map { e =>
      generated.map(p => e.bindings.find(_.param.name == p.name).flatMap(b => Try(Bindings.within(e.bindings)(b.value())).toOption)).toVector ++
        Vector(Some(e.a), Some(e.b))
    }

    private def generate(seed: Long, i: Int, size: Int): Vector[Any] =
      val d = Draw(random(seed, i), size, plan)
      if exampleCases.nonEmpty && d.chance(0.35) then
        val base = exampleCases(d.below(exampleCases.size)).zip(types).map((v, t) => v.getOrElse(d.value(t)))
        val k = d.below(types.size)
        if d.chance(0.25) then base
        else base.updated(k, (if plan.holdsOnly(types(k)) then Nil else Probes.near(base(k), plan.numbers)) match
          case Nil  => d.value(types(k))
          case near => if d.chance(0.5) then near(d.below(near.size)) else d.value(types(k)))
      else types.map(d.value)

    private def shown(vals: Vector[Any], r: Option[Any]): String =
      val (a, b) = (vals(generated.size), vals(generated.size + 1))
      val world = generated.zip(vals).map((p, v) => s"${p.name} = ${Example.show(v)}")
      s"(${Example.show(a)}, ${Example.show(b)}) ⇒ ${r.fold("no result")(Example.show)}" +
        (if world.isEmpty then "" else s"  given ${world.mkString(", ")}")

    @tailrec private def shrink(vals: Vector[Any], why: String, rounds: Int): (Vector[Any], String) =
      val smaller = LazyList.from(types.indices)
        .flatMap(i => Shrink.of(types(i), vals(i), opaques, plan.only).take(40).map(v => vals.updated(i, v)))
        .take(400).map(c => c -> attempt(c, None)._2).collectFirst { case (c, Some(w)) => (c, w) }
      smaller match
        case Some((c, w)) if rounds > 0 => shrink(c, w, rounds - 1)
        case _ => (vals, why)

    def report(settings: TestSettings, replay: List[Replay]): Report =
      val counter = Counter(() => Draw(random(settings.seed, -1), 3, plan))
      // The examples first: what they reach counts (what fails of them, their own check says).
      n.cases.filter(_.expected).foreach(e => Try(on(e.bindings, e.a, e.b, Some(counter))))
      // The cases that failed before, then new ones, small to large.
      val order = replay ++ (0 until settings.cases).map(i => Replay(settings.seed, i, sizeOf(i, settings.cases)))
      val failure = order.iterator.flatMap { c =>
        Try(generate(c.seed, c.index, c.size)).toOption.flatMap { vals =>
          attempt(vals, Some(counter))._2.map { why =>
            val (small, w) = shrink(vals, why, 100)
            Failed(shown(small, attempt(small, None)._1), w, c.seed, c.index, c.size)
          }
        }
      }.nextOption().orElse(Option.when((calledOps.toSet -- named).nonEmpty) {
        val unnamed = (calledOps.toSet -- named).toList.sorted.mkString(", ")
        Failed("", s"its code calls $unnamed, which it does not name: implement(${n.id}, $unnamed)(…), so the model shows what the code rests on",
          settings.seed, -1, 0)
      })
      val coverage = targets.map((t, o, text) => Covered(text, counter.held(t, o))).distinctBy(_.part)
      val notes = List(
        Option.when(counter.sampled.nonEmpty)(s"forall/exists over ${counter.sampled.mkString(", ")}: sampled, not every value"),
        Option.when(fixed.nonEmpty)(s"${fixed.map(_.param.name).mkString(", ")}: the examples' value (no Lean type to generate it from)"),
        Option.when(generated.isEmpty && n.cases.isEmpty)("nothing to vary: no examples, and the contract reads no parameter")
      ).flatten ++ customs.toList.map((t, g) => s"${Types.scala(t)}: ${g.describe} " +
        (if plan.only(t) then "(given: what the outside holds, with the examples' values)" else "(given; derived values for a quarter of them)")) ++
        unreached(settings)
      Report(settings.cases, settings.seed, against, failure, coverage, notes)

    /** A given generator's correspondence with the examples: the examples' values it never makes (kept as seeds). */
    private def unreached(settings: TestSettings): List[String] =
      customs.toList.flatMap { (t, g) =>
        val made: Set[Any] = (0 until 200).flatMap(i => Try(g.draw(Draw(random(settings.seed + 7, i), 5, plan))).toOption).toSet
        val missed = plan.seedsOf(t).filterNot(made)
        Option.when(missed.nonEmpty)(s"${Types.scala(t)}: the examples' ${missed.take(3).map(Example.show).mkString(", ")} never come from the given generator (kept as seeds)")
      }

/** The parts of a formula, or of a model's steps, a test must reach: an implication's premise, each side of an or, each
  * branch, each case of a match, and each list or option a `forall`/`exists` ranges over, not empty.
  */
private[frflow] object Coverage:
  def targets(root: Tree, print: Tree => String): List[(Tree, Int, String)] =
    def text(t: Tree) = { val s = print(t); if s.length > 120 then s.take(117) + "…" else s }
    def walk(t: Tree): List[(Tree, Int, String)] =
      val here = t match
        case Tree.Op(Prim.Implies, List(a, _)) => List((t, 1, s"${text(a)} held"))
        case Tree.Op(Prim.Or, List(a, b))      => List((t, 1, s"${text(a)} held"), (t, 2, s"${text(b)} held"))
        case Tree.If(c, _, _)                  => List((t, 1, s"${text(c)} held"), (t, 2, s"${text(c)} did not hold"))
        case Tree.Match(on, arms)              => arms.zipWithIndex.map((arm, i) => (t, i + 1, s"${text(on)} was ${pattern(arm.pat)}"))
        case Tree.Over(k, on, _, _) if Set(Iter.All, Iter.Some, Iter.OptAll, Iter.OptSome)(k) => List((t, 1, s"${text(on)} was not empty"))
        case _                                 => Nil
      here ++ children(t).flatMap(walk)
    walk(root)

  /** A model's steps: each branch taken either way, and the parts of the terms they compute. */
  def targets(s: Steps, print: Tree => String): List[(Tree, Int, String)] =
    val branches = Steps.fold(s, List.empty[(Tree, Int, String)]) {
      case (acc, Steps.Branch(c, _, _)) => acc ++ List((c, 1, s"${print(c)} held"), (c, 2, s"${print(c)} did not hold"))
      case (acc, _)                     => acc
    }
    branches ++ Trees.trees(s).flatMap(targets(_, print))

  private def pattern(p: Pat): String = p match
    case Pat.Ctor(_, c, _) => c.label
    case Pat.SomeP(_)      => "some value"
    case Pat.NoneP         => "none"
    case Pat.ConsP(_, _)   => "not empty"
    case Pat.NilP          => "empty"

  private def children(t: Tree): List[Tree] = t match
    case Tree.Call(_, as)        => as
    case Tree.Apply(f, as)       => f :: as
    case Tree.Fun(_, b)          => List(b)
    case Tree.Quant(_, _, b)     => List(b)
    case Tree.If(c, a, b)        => List(c, a, b)
    case Tree.Match(on, arms)    => on :: arms.map(_.body)
    case Tree.Let(_, v, b)       => List(v, b)
    case Tree.Field(on, _, _)    => List(on)
    case Tree.Copy(on, _, us)    => on :: us.map(_._2)
    case Tree.Make(_, _, as)     => as
    case Tree.Tup(es)            => es
    case Tree.Proj(on, _, _)     => List(on)
    case Tree.SomeT(a)           => List(a)
    case Tree.ListT(es)          => es
    case Tree.Over(_, on, _, b)  => List(on, b)
    case Tree.Op(_, as)          => as
    case _                       => Nil

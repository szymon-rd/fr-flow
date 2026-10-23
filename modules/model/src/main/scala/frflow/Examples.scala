package frflow

import scala.util.Try

/** A concrete case of a contract, under given parameter values: the call `(a, b)` with `result`. */
final case class Example(note: String, bindings: List[Binding], givenSource: List[String], a: Any, b: Any, result: Any, expected: Boolean):
  def call: String = s"(${Example.show(a)}, ${Example.show(b)}) ⇒ ${Example.show(result)}"
  def givens: List[String] = bindings.zip(givenSource).map { (b, src) =>
    val v = Bindings.within(bindings)(b.value())
    if Example.isData(v) then s"${b.param.name} = ${Example.show(v)}" else src
  }
  def describe: String = s"${if expected then "expect" else "reject"} $call  given ${givens.mkString(", ")}  — $note"

object Example:
  def show(v: Any): String = v match
    case s: String => "\"" + s + "\""
    case None      => "None"
    case Some(x)   => s"Some(${show(x)})"
    case l: List[?] => l.map(show).mkString("List(", ", ", ")")
    case m: Map[?, ?] => m.map((k, x) => s"${show(k)} -> ${show(x)}").mkString("Map(", ", ", ")")
    case p: Product if p.productArity > 0 =>
      p.productPrefix + p.productIterator.map(show).mkString("(", ", ", ")")
    case other => String.valueOf(other)

  private def isData(v: Any): Boolean = v match
    case _: String | _: Boolean | _: Int | _: Long | _: BigInt | _: Char => true
    case o: Option[?] => o.forall(isData)
    case i: Iterable[?] => i.forall(isData)
    case p: Product => !p.getClass.getName.contains("$$Lambda") && p.productIterator.forall(isData)
    case _ => false

  private[frflow] object NoResult:
    override def toString: String = "no result"

final case class Case[A, B, R](a: A, b: B, result: R, expected: Boolean, note: String)
/** A run of a flow: its input, the world before, its result and the world after. */
final case class FlowCase[A, R](a: A, before: World, result: R, after: World, expected: Boolean, note: String)

/** The contract accepts this result, and the implementation must return it. */
def expect[A, B, R](a: A, b: B, result: R, note: String): Case[A, B, R] = Case(a, b, result, true, note)

/** The contract must refuse this result. */
def reject[A, B, R](a: A, b: B, result: R, note: String): Case[A, B, R] = Case(a, b, result, false, note)

/** A run the flow's contract accepts, and its code (run on the models) must make. */
def expect[A, R](a: A, before: World, result: R, after: World, note: String): FlowCase[A, R] = FlowCase(a, before, result, after, true, note)
/** A run the flow's contract must refuse. */
def reject[A, R](a: A, before: World, result: R, after: World, note: String): FlowCase[A, R] = FlowCase(a, before, result, after, false, note)

/** The outcome of one example: against the contract, and against the implementation. */
final case class ExampleResult(example: Example, contract: String, implementation: Option[String]):
  def verdict: String =
    val ws = List(Option.when(contract != "ok")(contract), implementation.filter(_ != "ok").map(i => s"the implementation $i")).flatten
    if ws.isEmpty then "ok" else ws.mkString("; ")

// The examples run the developer's code: what it throws is a finding about that code, said in the verdict
// ("error: …"), never a failure of the run.
private def verdict(t: Try[String]): String = t.fold(e => s"error: ${e.getMessage}", identity)

extension [A, B, R](n: Node[(A, B) => R])
  def checkExamples(impl: Option[() => (A, B) => R], assumes: List[Assumption] = Nil): List[ExampleResult] =
    n.postFn.toList.flatMap { post =>
      // The implementation is built once per set of given values, as a running system would be.
      type Built = Map[List[Binding], Try[(A, B) => R]]
      n.cases.foldLeft((Map.empty: Built, Vector.empty[ExampleResult])) { case ((built, out), e) =>
        val (a, b, r) = (e.a.asInstanceOf[A], e.b.asInstanceOf[B], e.result.asInstanceOf[R])
        Bindings.within(e.bindings) {
          val onContract = verdict(Try {
            val ok = post(a, b, r)
            assumes.find(x => x.reads.forall(p => e.bindings.exists(_.param.name == p)) && !x.holds()) match
              case Some(x)                   => s"the values it gives break the assumption ${x.what}"
              case None if ok != e.expected => if e.expected then "the contract refuses it" else "the contract accepts it"
              case None if e.expected        => n.broken(a, b, r).fold("ok")(i => s"the invariant $i refuses it")
              case None                      => "ok"
          })
          def returned(got: R): String =
            n.broken(a, b, got).map(i => s"returned ${Example.show(got)}, which breaks the invariant $i")
              .getOrElse(if e.expected == (got == r) then "ok" else s"returned ${Example.show(got)}")
          val code = impl.map(mk => built.getOrElse(e.bindings, Try(mk())))
          val onCode = code.map(c => verdict(c.flatMap(f => Try(returned(f(a, b))))))
          (code.fold(built)(built.updated(e.bindings, _)), out :+ ExampleResult(e, onContract, onCode))
        }
      }._2.toList
    }

/** Running a knowledge base's examples, and its code beyond them. */
private[frflow] object ExampleRuns:
  private type Untyped = Node[(Any, Any) => Any]
  private def untyped(n: Node[?]): Untyped = n.asInstanceOf[Untyped]

  def results(kb: KnowledgeBase, n: Node[?]): List[ExampleResult] =
    // An example need not bind the operations its code calls, nor the defined terms: they run as in service.
    if n.cases.isEmpty then Nil
    else Bindings.within(kb.opCode ++ kb.definitionBindings) {
      untyped(n).checkExamples(kb.implementation(n).map(_.factory.asInstanceOf[() => (Any, Any) => Any]), kb.runtimeAssumptions) ++
        generated(kb, n) ++ onReal(kb, n)
    }

  /** A flow's examples run on the production implementations of its boundaries, started in each model's state before:
    * what they give, read back, must be what the run on the models gives.
    */
  private def onReal(kb: KnowledgeBase, n: Node[?]): List[ExampleResult] =
    (for
      flow <- kb.implementation(n).flatMap(_.flowDef)
      (bs, body) = flow.lifted.built
      steps <- body.termTree match { case Tree.Do(s) => Some(s); case _ => None }
      reals = kb.models.filter(m => m.real.isDefined && Steps.boundaries(steps).contains(m.boundary))
      if reals.nonEmpty
    yield n.cases.filter(_.expected).flatMap { e =>
      val before = e.b.asInstanceOf[World]
      val model = Try(Flows.onModels(steps, Map(bs.head -> e.a), before))
      val real = Try {
        val impls = reals.map(m => m.boundary -> m.real.get._1(before(m.model.asInstanceOf[StateModel[Any]]))).toMap
        val r = Flows.runNow(steps, Map(bs.head -> e.a), impls)
        (r, reals.foldLeft(before)((w, m) => w.updated(m.model, m.real.get._2(impls(m.boundary)))))
      }
      val verdict = (model, real) match
        case (scala.util.Success(m), scala.util.Success(r)) if m == r => "ok"
        case (scala.util.Success(m), scala.util.Success(r)) =>
          s"on ${reals.map(_.boundary.name).mkString(", ")} gives ${Example.show(r)}, where the model gives ${Example.show(m)}"
        case (_, scala.util.Failure(x)) => s"error on ${reals.map(_.boundary.name).mkString(", ")}: ${x.getMessage}"
        case (scala.util.Failure(x), _) => s"error on the models: ${x.getMessage}"
      List(ExampleResult(e.copy(note = s"${e.note} (run on ${reals.map(_.boundary.name).mkString(", ")})"), "ok", Some(verdict)))
    }).getOrElse(Nil)

  // On `loose` (varied) data, a result in another order than the define's is the same result, and data the
  // outside cannot hold (two rows with one key) is no finding.
  private final case class Given(bindings: List[Binding], sources: List[String], loose: Boolean)

  /** The calls (at most ten) on every combination of the examples' inputs whose result breaks the contract. */
  def generated(kb: KnowledgeBase, n: Node[?]): List[ExampleResult] =
    val c = untyped(n)
    (for { i <- kb.implementation(n); post <- c.postFn if n.cases.nonEmpty } yield failures(c, i, post)).getOrElse(Nil)

  private def failures(n: Untyped, i: Implementation, post: (Any, Any, Any) => Boolean): List[ExampleResult] =
    val known = n.cases.map(e => (e.bindings, e.a, e.b)).toSet
    // Once per set of parameter values: examples giving them in the same words are one group (a value with
    // no structural equality, a database, is never equal to another).
    val groups = n.cases.map(e => Given(e.bindings, e.givenSource, loose = false)).distinctBy(_.sources)
    // Code beside a proven define must return what the define returns; run on varied data too, a query that drops
    // rows or reads the wrong column is found where the examples' data hides it.
    val besideDefine = i.proven.isDefined && !i.provenCode
    val varied = if besideDefine then groups.flatMap(vary(_, n.cases)) else Nil
    (groups ++ varied).flatMap { g =>
      Bindings.within(g.bindings) {
        val reference = if besideDefine then i.proven.map(_.lifted.value.asInstanceOf[(Any, Any) => Any]) else None
        Try(i.factory.asInstanceOf[() => (Any, Any) => Any]()).toOption.toList.flatMap { impl =>
          Probes.combinations(n.cases).filter((a, b) => reference.isDefined || !known((g.bindings, a, b))).flatMap { (a, b) =>
            val (r, why) = finding(n, post, impl, reference, g.loose, a, b)
            why.map(w => ExampleResult(Example("generated from the examples' inputs: the contract holds for every call", g.bindings,
              g.sources, a, b, r, true), "ok", Some(w)))
          }
        }
      }
    }.distinctBy(r => (r.example.a, r.example.b, r.implementation)).take(10)

  private def vary(g: Given, cases: List[Example]): List[Given] =
    g.bindings.flatMap { b =>
      Try(Bindings.within(g.bindings)(b.value())).toOption.toList.flatMap(Probes.variations(_, cases)).map { v =>
        Given(g.bindings.map(x => if x eq b then Binding(b.param, () => v) else x),
          g.sources.map(_ + s" (${b.param.name} varied: ${Example.show(v)})"), loose = true)
      }
    }

  private def finding(n: Untyped, post: (Any, Any, Any) => Boolean, impl: (Any, Any) => Any, reference: Option[(Any, Any) => Any],
      loose: Boolean, a: Any, b: Any): (Any, Option[String]) =
    Try {
      val r = impl(a, b)
      val keeps = n.broken(a, b, r)
      val expected = reference.map(_(a, b)).filterNot(same(_, r, loose))
      (r, expected.map(x => s"returned ${Example.show(r)}, where the proven define returns ${Example.show(x)}")
        .orElse(Option.when(!post(a, b, r))(s"returned ${Example.show(r)}, which breaks the contract"))
        .orElse(keeps.map(i => s"returned ${Example.show(r)}, which breaks the invariant $i")))
    }.fold(e => (Example.NoResult, Option.when(!loose)(s"error: ${e.getMessage}")), identity)

  private def same(x: Any, y: Any, loose: Boolean): Boolean = (x, y) match
    case (xs: List[?], ys: List[?]) if loose => xs.size == ys.size && xs.diff(ys).isEmpty
    case _ => x == y

/** The one generator of inputs and values near the examples', for Lean's probes and for the code's runs. */
object Probes:
  def numbers(v: Any): List[BigInt] = v match
    case i: Int     => List(BigInt(i))
    case l: Long    => List(BigInt(l))
    case b: BigInt  => List(b)
    case l: Iterable[?] => l.toList.flatMap(numbers)
    case Some(x)    => numbers(x)
    case p: Product => p.productIterator.toList.flatMap(numbers)
    case _          => Nil
  def boundaries(cases: List[Example]): List[BigInt] = cases.flatMap(e => numbers(e.a) ++ numbers(e.b)).distinct

  /** Values near `v`: a number at the boundaries and next to them, a list shortened, reversed or grown, a field changed. */
  def near(v: Any, nums: List[BigInt]): List[Any] =
    val out: List[Any] = v match
      case b: Boolean => List(!b)
      case i: Int     => (nums.filter(_.isValidInt).map(_.toInt) ++ List(0, i + 1, i - 1, -i))
      case l: Long    => (nums.filter(_.isValidLong).map(_.toLong) ++ List(0L, l + 1, l - 1, -l))
      case b: BigInt  => nums ++ List(BigInt(0), b + 1, b - 1, -b)
      case s: String  => List("", s + s)
      case Some(x)    => None :: near(x, nums).take(2).map(Some(_))
      case l: List[?] => if l.isEmpty then Nil else List(Nil, l.tail, l.reverse, l.head :: l) ++ near(l.head, nums).take(2).map(x => l :+ x)
      case p: Product if p.productArity > 0 =>
        val fields = p.productIterator.toList
        p.getClass.getConstructors.find(_.getParameterCount == fields.size).toList.flatMap(k => fields.indices.flatMap(i =>
          near(fields(i), nums).take(3).flatMap(x => Try(k.newInstance(fields.updated(i, x).map(_.asInstanceOf[AnyRef])*)).toOption)))
      case _ => Nil
    out.distinct.filter(_ != v)

  /** Inputs near the examples' that no example asks: what Lean probes evaluate. */
  def inputs(cases: List[Example]): List[(Any, Any)] =
    val nums = boundaries(cases)
    val asked = cases.map(e => (e.a, e.b)).toSet
    cases.flatMap(e => for { a <- e.a :: near(e.a, nums); b <- e.b :: near(e.b, nums) } yield (a, b)).distinct.filterNot(asked)
  def combinations(cases: List[Example]): List[(Any, Any)] =
    for a <- cases.map(_.a).distinct; b <- cases.map(_.b).distinct yield (a, b)
  /** Near a parameter value an example gives (a table with a row dropped, repeated or changed). */
  def variations(v: Any, cases: List[Example]): List[Any] = near(v, boundaries(cases) ++ numbers(v)).take(8)

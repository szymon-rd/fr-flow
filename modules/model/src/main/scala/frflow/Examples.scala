package frflow

import scala.util.Try

/** A concrete case of a contract, under given parameter values: the call `(a, b)`
  * with `result`. An `expect`ed case must be accepted by the contract and returned by
  * the implementation; a `reject`ed one must be refused by the contract.
  */
final case class Example(note: String, bindings: List[Binding], givenSource: List[String], a: Any, b: Any, result: Any, expected: Boolean):
  def call: String = s"(${Example.show(a)}, ${Example.show(b)}) ⇒ ${Example.show(result)}"

  /** The parameter values, as values where they print as such (functions as their source). */
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

  /** Whether a value prints as itself: data, not a function or a connection. */
  private def isData(v: Any): Boolean = v match
    case _: String | _: Boolean | _: Int | _: Long | _: BigInt | _: Char => true
    case o: Option[?] => o.forall(isData)
    case i: Iterable[?] => i.forall(isData)
    case p: Product => !p.getClass.getName.contains("$$Lambda") && p.productIterator.forall(isData)
    case _ => false

  /** The result of a generated call whose code failed: there is none. */
  private[frflow] object NoResult:
    override def toString: String = "no result"

/** One case of `examples`. */
final case class Case[A, B, R](a: A, b: B, result: R, expected: Boolean, note: String)

/** The contract accepts this result, and the implementation must return it. */
def expect[A, B, R](a: A, b: B, result: R, note: String): Case[A, B, R] = Case(a, b, result, true, note)

/** The contract must refuse this result. */
def reject[A, B, R](a: A, b: B, result: R, note: String): Case[A, B, R] = Case(a, b, result, false, note)

/** The outcome of one example: against the contract, and against the implementation if one is registered. */
final case class ExampleResult(example: Example, contract: String, implementation: Option[String]):
  /** In words: "ok", or what went wrong, of the contract and of the implementation. */
  def verdict: String =
    List(Option.when(contract != "ok")(contract), implementation.filter(_ != "ok").map(i => s"the implementation $i")).flatten match
      case Nil => "ok"
      case ws  => ws.mkString("; ")

// The examples run the developer's code: what it throws is a finding about that code, said in the
// verdict ("error: …"), never a failure of the run.
private def verdict(t: Try[String]): String = t.fold(e => s"error: ${e.getMessage}", identity)

extension [A, B, R](n: Node[(A, B) => R])
  /** Each example, checked against the contract and, if given, against an implementation
    * built under the example's parameter values.
    */
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

  /** The results of a node's examples, against the implementation when one is registered, then the
    * generated calls its code fails.
    */
  def results(kb: KnowledgeBase, n: Node[?]): List[ExampleResult] =
    // An example need not bind the operations its code calls, nor the defined terms: they run as in service.
    if n.cases.isEmpty then Nil
    else Bindings.within(kb.opCode ++ kb.definitionBindings) {
      untyped(n).checkExamples(kb.implementation(n).map(_.factory.asInstanceOf[() => (Any, Any) => Any]), kb.runtimeAssumptions) ++
        generated(kb, n)
    }

  /** Parameter values a group of calls runs under, as the examples give them (`sources`). On `loose`
    * (varied) data, a result in another order than the define's is the same result, and data the
    * outside cannot hold (two rows with one key) is no finding.
    */
  private final case class Given(bindings: List[Binding], sources: List[String], loose: Boolean)

  /** The contract holds for every call, not only the examples: the implementation also runs on
    * every combination of the examples' inputs, under each example's parameter values. The calls
    * whose result breaks the contract are listed (at most ten).
    */
  def generated(kb: KnowledgeBase, n: Node[?]): List[ExampleResult] =
    val c = untyped(n)
    (for
      i    <- kb.implementation(n)
      post <- c.postFn
      if n.cases.nonEmpty
    yield failures(c, i, post)).getOrElse(Nil)

  private def failures(n: Untyped, i: Implementation, post: (Any, Any, Any) => Boolean): List[ExampleResult] =
    val known = n.cases.map(e => (e.bindings, e.a, e.b)).toSet
    // Once per set of parameter values: examples giving them in the same words are one group (a value
    // with no structural equality, a database, is never equal to another).
    val groups = n.cases.map(e => Given(e.bindings, e.givenSource, loose = false)).distinctBy(_.sources)
    // Code that runs beside a proven define returns what the define returns, examples included; it is
    // also run on varied data (`Probes.variations`), so a query that drops rows or reads the wrong
    // column is found where the examples' data hides it.
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

  /** The group with one parameter's value varied, for each value and each variation of it. */
  private def vary(g: Given, cases: List[Example]): List[Given] =
    g.bindings.flatMap { b =>
      Try(Bindings.within(g.bindings)(b.value())).toOption.toList.flatMap(Probes.variations(_, cases)).map { v =>
        Given(g.bindings.map(x => if x eq b then Binding(b.param, () => v) else x),
          g.sources.map(_ + s" (${b.param.name} varied: ${Example.show(v)})"), loose = true)
      }
    }

  /** What the call `(a, b)` returns, and what is wrong with it, if anything. */
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
    case (xs: List[?], ys: List[?]) if loose => xs.size == ys.size && counts(xs) == counts(ys)
    case _ => x == y

  private def counts(xs: List[?]): Map[Any, Int] = xs.groupMapReduce(identity)(_ => 1)(_ + _)

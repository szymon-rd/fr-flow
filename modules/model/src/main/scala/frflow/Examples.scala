package frflow

import scala.util.Try

/** A concrete case of a contract, under given parameter values: the call on `inputs` with `result`. A flow's run has the
  * world before as its last input, and the pair of its result and the world after as its result.
  */
final case class Example(note: String, bindings: List[Binding], givenSource: List[String], inputs: List[Any], result: Any, expected: Boolean):
  def call: String = s"${inputs.map(Example.show).mkString("(", ", ", ")")} ⇒ ${Example.show(result)}"
  def givens: List[String] = bindings.zip(givenSource).map { (b, src) =>
    val v = Bindings.within(bindings)(b.value())
    if Example.isData(v) then s"${b.param.name} = ${Example.show(v)}" else src
  }
  def describe: String = s"${if expected then "expect" else "reject"} $call  given ${givens.mkString(", ")}  — $note"

object Example:
  def show(v: Any): String = v match
    case s: String => "\"" + s + "\""
    case t: Table  => t.shown
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

/** A case of a contract on an operation of type `F`: a call's inputs and result; a flow's run, its inputs and the world
  * before, and its result with the world after.
  */
final case class Case[F] private[frflow] (inputs: List[Any], result: Any, expected: Boolean, note: String)

// `expect`: the contract accepts this result, and the implementation must return it. `reject`: the contract must refuse it.
// One of each per number of inputs; a flow's run takes the world before after its inputs, and the world after its result.
def expect[R](result: R, note: String): Case[() => R] = Case(Nil, result, true, note)
def reject[R](result: R, note: String): Case[() => R] = Case(Nil, result, false, note)
def expect[A, R](a: A, result: R, note: String): Case[A => R] = Case(List(a), result, true, note)
def reject[A, R](a: A, result: R, note: String): Case[A => R] = Case(List(a), result, false, note)
def expect[A, B, R](a: A, b: B, result: R, note: String): Case[(A, B) => R] = Case(List(a, b), result, true, note)
def reject[A, B, R](a: A, b: B, result: R, note: String): Case[(A, B) => R] = Case(List(a, b), result, false, note)
def expect[A, B, C, R](a: A, b: B, c: C, result: R, note: String): Case[(A, B, C) => R] = Case(List(a, b, c), result, true, note)
def reject[A, B, C, R](a: A, b: B, c: C, result: R, note: String): Case[(A, B, C) => R] = Case(List(a, b, c), result, false, note)
def expect[A, B, C, D, R](a: A, b: B, c: C, d: D, result: R, note: String): Case[(A, B, C, D) => R] =
  Case(List(a, b, c, d), result, true, note)
def reject[A, B, C, D, R](a: A, b: B, c: C, d: D, result: R, note: String): Case[(A, B, C, D) => R] =
  Case(List(a, b, c, d), result, false, note)
def expect[A, B, C, D, E, R](a: A, b: B, c: C, d: D, e: E, result: R, note: String): Case[(A, B, C, D, E) => R] =
  Case(List(a, b, c, d, e), result, true, note)
def reject[A, B, C, D, E, R](a: A, b: B, c: C, d: D, e: E, result: R, note: String): Case[(A, B, C, D, E) => R] =
  Case(List(a, b, c, d, e), result, false, note)
def expect[A, B, C, D, E, X, R](a: A, b: B, c: C, d: D, e: E, x: X, result: R, note: String): Case[(A, B, C, D, E, X) => R] =
  Case(List(a, b, c, d, e, x), result, true, note)
def reject[A, B, C, D, E, X, R](a: A, b: B, c: C, d: D, e: E, x: X, result: R, note: String): Case[(A, B, C, D, E, X) => R] =
  Case(List(a, b, c, d, e, x), result, false, note)

def expect[R](before: World, result: R, after: World, note: String): Case[() => Flow[R]] =
  Case(List(before), (result, after), true, note)
def reject[R](before: World, result: R, after: World, note: String): Case[() => Flow[R]] =
  Case(List(before), (result, after), false, note)
def expect[A, R](a: A, before: World, result: R, after: World, note: String): Case[A => Flow[R]] =
  Case(List(a, before), (result, after), true, note)
def reject[A, R](a: A, before: World, result: R, after: World, note: String): Case[A => Flow[R]] =
  Case(List(a, before), (result, after), false, note)
def expect[A, B, R](a: A, b: B, before: World, result: R, after: World, note: String): Case[(A, B) => Flow[R]] =
  Case(List(a, b, before), (result, after), true, note)
def reject[A, B, R](a: A, b: B, before: World, result: R, after: World, note: String): Case[(A, B) => Flow[R]] =
  Case(List(a, b, before), (result, after), false, note)
def expect[A, B, C, R](a: A, b: B, c: C, before: World, result: R, after: World, note: String): Case[(A, B, C) => Flow[R]] =
  Case(List(a, b, c, before), (result, after), true, note)
def reject[A, B, C, R](a: A, b: B, c: C, before: World, result: R, after: World, note: String): Case[(A, B, C) => Flow[R]] =
  Case(List(a, b, c, before), (result, after), false, note)
def expect[A, B, C, D, R](a: A, b: B, c: C, d: D, before: World, result: R, after: World, note: String): Case[(A, B, C, D) => Flow[R]] =
  Case(List(a, b, c, d, before), (result, after), true, note)
def reject[A, B, C, D, R](a: A, b: B, c: C, d: D, before: World, result: R, after: World, note: String): Case[(A, B, C, D) => Flow[R]] =
  Case(List(a, b, c, d, before), (result, after), false, note)
def expect[A, B, C, D, E, R](a: A, b: B, c: C, d: D, e: E, before: World, result: R, after: World, note: String)
    : Case[(A, B, C, D, E) => Flow[R]] = Case(List(a, b, c, d, e, before), (result, after), true, note)
def reject[A, B, C, D, E, R](a: A, b: B, c: C, d: D, e: E, before: World, result: R, after: World, note: String)
    : Case[(A, B, C, D, E) => Flow[R]] = Case(List(a, b, c, d, e, before), (result, after), false, note)
def expect[A, B, C, D, E, X, R](a: A, b: B, c: C, d: D, e: E, x: X, before: World, result: R, after: World, note: String)
    : Case[(A, B, C, D, E, X) => Flow[R]] = Case(List(a, b, c, d, e, x, before), (result, after), true, note)
def reject[A, B, C, D, E, X, R](a: A, b: B, c: C, d: D, e: E, x: X, before: World, result: R, after: World, note: String)
    : Case[(A, B, C, D, E, X) => Flow[R]] = Case(List(a, b, c, d, e, x, before), (result, after), false, note)

/** The outcome of one example: against the contract, and against the implementation. */
final case class ExampleResult(example: Example, contract: String, implementation: Option[String]):
  def verdict: String =
    val ws = List(Option.when(contract != "ok")(contract), implementation.filter(_ != "ok").map(i => s"the implementation $i")).flatten
    if ws.isEmpty then "ok" else ws.mkString("; ")

// The examples run the developer's code: what it throws is a finding about that code, said in the verdict
// ("error: …"), never a failure of the run.
private def verdict(t: Try[String]): String = t.fold(e => s"error: ${e.getMessage}", identity)

extension (n: Node[?])
  /** Each example against the contract, and against `impl` (code built once per set of given values, as a running
    * system would build it: a Scala function of the call's inputs).
    */
  private[frflow] def checkExamples(impl: Option[() => Any], assumes: List[Assumption] = Nil): List[ExampleResult] =
    n.postFn.toList.flatMap { post =>
      type Built = Map[List[Binding], Try[Any]]
      n.cases.foldLeft((Map.empty: Built, Vector.empty[ExampleResult])) { case ((built, out), e) =>
        val (ins, r) = (e.inputs, e.result)
        Bindings.within(e.bindings) {
          val onContract = verdict(Try {
            val ok = post(ins, r)
            assumes.find(x => x.reads.forall(p => e.bindings.exists(_.param.name == p)) && !x.holds()) match
              case Some(x)                   => s"the values it gives break the assumption ${x.what}"
              case None if ok != e.expected => if e.expected then "the contract refuses it" else "the contract accepts it"
              case None if e.expected        => n.broken(ins, r).fold("ok")(i => s"the invariant $i refuses it")
              case None                      => "ok"
          })
          def returned(got: Any): String =
            n.broken(ins, got).map(i => s"returned ${Example.show(got)}, which breaks the invariant $i")
              .getOrElse(if e.expected == (got == r) then "ok" else s"returned ${Example.show(got)}")
          val code = impl.map(mk => built.getOrElse(e.bindings, Try(mk())))
          val onCode = code.map(c => verdict(c.flatMap(f => Try(returned(Fn.call(f, ins))))))
          (code.fold(built)(built.updated(e.bindings, _)), out :+ ExampleResult(e, onContract, onCode))
        }
      }._2.toList
    }

/** Running a knowledge base's examples, and its code beyond them. */
private[frflow] object ExampleRuns:
  def results(kb: KnowledgeBase, n: Node[?]): List[ExampleResult] =
    // An example need not bind the operations its code calls, nor the defined terms: they run as in service.
    if n.cases.isEmpty then Nil
    else Bindings.within(kb.opCode ++ kb.definitionBindings) {
      n.checkExamples(kb.implementation(n).map(_.factory), kb.runtimeAssumptions) ++
        onReal(kb, n)
    }

  /** A flow's examples run on each implementation of its boundaries (an outside system, or the project's own), started in
    * each model's state before: what they give, read back, must be what the run on the models gives. Both are compared
    * as the implementation holds a state: the model runs from the example's state stored and read back, and its state
    * after is stored in a fresh implementation and read back. What the implementation does not keep (the order of rows a
    * table returns sorted) is then not compared; what it keeps (the order of an event log) is.
    */
  private def onReal(kb: KnowledgeBase, n: Node[?]): List[ExampleResult] =
    (for
      flow <- kb.implementation(n).flatMap(_.flowDef).toList
      (bs, body) = flow.lifted.built
      steps <- (body.termTree match { case Tree.Do(s) => Some(s); case _ => None }).toList
      mo <- kb.models.filter(m => Steps.boundaries(steps).contains(m.boundary))
      impl <- mo.impls
      e <- n.cases.filter(_.expected)
    yield
      val m = mo.model.asInstanceOf[StateModel[Any]]
      val (args, before) = (e.inputs.init, e.inputs.last.asInstanceOf[World])
      def held(w: World): World = w.updated(m, impl.read(impl.start(w(m))))
      val name = ModelTests.implName(impl)
      // Under the example's own values too: the operations the flow calls read them.
      val model = Bindings.within(e.bindings)(Try(Flows.onModels(steps, bs.zip(args).toMap, held(before))).map((r, w) => (r, held(w))))
      val real = Bindings.within(e.bindings)(Try {
        val i = impl.start(before(m))
        val r = Flows.runNow(steps, bs.zip(args).toMap, Map(mo.boundary -> i))
        (r, before.updated(m, impl.read(i)))
      })
      val verdict = (model, real) match
        case (scala.util.Success(x), scala.util.Success(y)) if x == y => "ok"
        case (scala.util.Success(x), scala.util.Success(y)) => s"on $name gives ${Example.show(y)}, where the model gives ${Example.show(x)}"
        case (_, scala.util.Failure(x)) => s"error on $name: ${x.getMessage}"
        case (scala.util.Failure(x), _) => s"error on the models: ${x.getMessage}"
      ExampleResult(e.copy(note = s"${e.note} (run on $name)"), "ok", Some(verdict))
    )

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
  def boundaries(cases: List[Example]): List[BigInt] = cases.flatMap(_.inputs.flatMap(numbers)).distinct

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

  /** Inputs near the examples' that no example asks: what Lean probes evaluate. Each input is the example's or one near
    * it, the first input varying slowest.
    */
  def inputs(cases: List[Example]): List[List[Any]] =
    val nums = boundaries(cases)
    val asked = cases.map(_.inputs).toSet
    def calls(choices: List[List[Any]]): List[List[Any]] =
      choices.foldRight(List(List.empty[Any]))((xs, rest) => for x <- xs; r <- rest yield x :: r)
    cases.flatMap(e => calls(e.inputs.map(x => x :: near(x, nums)))).distinct.filterNot(asked)

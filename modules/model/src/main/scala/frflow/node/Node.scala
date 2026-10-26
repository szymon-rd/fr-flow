package frflow
package node

import frflow.example.ExampleRuns
import frflow.program.ContractMacros
import frflow.protocol.{NodeKind, RunCheck}
import frflow.runtime.RunTimeChecks
import frflow.types.Shape
import java.util.concurrent.atomic.AtomicReference
import scala.util.Try

/** One statement in the developer's domain words, decided by them and proven in Lean from its parts (the nodes
  * that name it in `refines`). `M` is the operation's type, which the examples and checks are written against.
  */
final class Node[M] @scala.annotation.publicInBinary private[frflow] (val id: String, val statement: String, val why: String,
    val kind: NodeKind, val declaredParents: List[Node[?]] = Nil, val formula: Option[Lifted[?]] = None,
    val post: Option[Lifted[?]] = None, val op: Option[Param[?]] = None, val rule: Option[Lifted[?]] = None,
    val substs: List[Subst] = Nil, val cases: List[Example] = Nil, val governs: List[String] = Nil, val kept: List[Keep] = Nil,
    val scope: List[Node[?]] = Nil, val ideaSection: String = "", val file: String = "", val expected: List[(String, Lifted[?])] = Nil,
    val at: Int = -1, val local: Option[Lifted[?]] = None, val replaced: Option[Node[?]] = None,
    val modelOf: Option[ModelOf] = None, val runCheck: Option[RunCheck] = None, val openAbove: Boolean = false,
    val failure: Option[FailureClause] = None):
  def parents: List[Node[?]] = (declaredParents ++ kept.collect { case Keep(i, Some(_), _) => i }).distinctBy(System.identityHashCode)
  def isInvariant: Boolean = rule.isDefined
  def shownKind: String = kind.shown(isInvariant)
  /** A contract on a flow: its operation runs from a world (`A => Flow[R]`), its post relates the worlds before and after. */
  def isFlow: Boolean = op.exists(o => o.termType.shape match { case Shape.FnOf(_, r) => r.shape.isInstanceOf[Shape.FlowOf]; case _ => false })
  /** The Lean type of the operation: a flow's that may fail gives its outcome, `Except E R`, and the world after. */
  private[frflow] def opType: Option[LeanType[?]] = op.map(o => (o.termType.shape, failure) match
    case (Shape.FnOf(as, r), Some(f)) => r.shape match
      case Shape.FlowOf(x) => LeanType.of(Shape.FnOf(as, LeanType.of(Shape.FlowOf(LeanType.of(Shape.EitherOf(f.err, x))))))
      case _               => o.termType
    case _ => o.termType)
  def defines: List[String] = substs.map(_.name)
  def referenced: List[Lifted[?]] = formula.toList ++ post.toList ++ rule.toList ++ local.toList ++ substs.flatMap(_.term) ++
    kept.flatMap(_.view) ++ expected.map(_._2) ++ failure.flatMap(_.post)

  // `require` in the builders: a node built from one declared after it gets `null` (Scala initializes vals in
  // order), and failing as the model loads, naming the node, is what the developer can act on.

  /** A part of each of `ps`: with its co-parts, it refines each. */
  def refines(ps: Node[?]*): Node[M] =
    require(ps.forall(_ != null), s"$id refines a node declared after it: declare the parent first")
    require(kind != NodeKind.Definition, s"$id: a definition has no parents; the nodes that use its terms rest on it")
    copy(declaredParents = declaredParents ++ ps)

  /** This contract fixes a word the nodes above leave open ("a share in force"): a node whose statement names its
    * operation holds whatever the operation does, so it does not rest on this contract even where its code calls the
    * operation. A change here (7 days become 14) brings back what is stated with the word fixed, not what is proven
    * for every meaning of it. Lean checks the code above again either way.
    */
  def leftOpenAbove: Node[M] =
    require(kind == NodeKind.Contract, s"$id: only a contract fixes a word left open above")
    copy(openAbove = true)

  /** A run of this flow may fail with an error of type `E` (a failing boundary's, or one it raises); one that fails
    * changes nothing: every model's state after it is as before. The post is what holds of a run that succeeds.
    */
  def failsChangingNothing[E](using e: LeanType[E]): Node[M] =
    require(isFlow, s"$id: only a contract on a flow says what holds when a run fails")
    copy(failure = Some(FailureClause(e, None)))

  /** A run of this flow may fail with an error of type `E`; `post(error, before, after)` holds of one that fails. */
  inline def onFailure[E](inline post: (Term[E], Term[World], Term[World]) => Term[Boolean])(using e: LeanType[E]): Node[M] =
    require(isFlow, s"$id: only a contract on a flow says what holds when a run fails")
    copy(failure = Some(FailureClause(e, Some(Lifted.lambda(post, List(e, summon[LeanType[World]], summon[LeanType[World]]), Source.text(post))))))

  /** An alternative to `other`: accepting one rejects the other. */
  def replaces(other: Node[?]): Node[M] =
    require(other != null, s"$id replaces a node declared after it: declare it first")
    copy(replaced = Some(other))

  /** A consequence the developer expects, which Lean proves from the claim: "Acme never sees Globex's contact". */
  inline def expects(statement: String)(inline consequence: Term[Boolean]): Node[M] =
    copy(expected = expected :+ (statement -> Lifted.thunk(() => consequence, Source.text(consequence))))

  private[frflow] def copy(declaredParents: List[Node[?]] = declaredParents, cases: List[Example] = cases, kept: List[Keep] = kept,
      expected: List[(String, Lifted[?])] = expected, local: Option[Lifted[?]] = local, replaced: Option[Node[?]] = replaced,
      modelOf: Option[ModelOf] = modelOf, runCheck: Option[RunCheck] = runCheck, openAbove: Boolean = openAbove,
      failure: Option[FailureClause] = failure): Node[M] =
    Node(id, statement, why, kind, declaredParents, formula, post, op, rule, substs, cases, governs, kept, scope, ideaSection,
      file, expected, at, local, replaced, modelOf, runCheck, openAbove, failure)

  /** The invariant does not apply to this contract or design decision, for the reason given (which the developer reads). */
  def exempt(invariant: Node[?], because: String): Node[M] =
    require(invariant != null, s"$id is exempt from an invariant declared after it: declare the invariant first")
    copy(kept = kept :+ Keep(invariant, None, because))
  override def toString: String = id

object Node:
  // Each is built in a method of its own: a file's top-level vals initialize in one JVM method (at most 64 KB).

  /** With no parents, the root: the idea's purpose, stated precisely enough that doing nothing does not meet it.
    * A claim, like a contract, needs no `why`: the reason it holds is kept with the developer's signed decision.
    */
  inline def claim(statement: String, why: String = "", idea: String = "")(inline formula: Term[Boolean]): Node[Unit] =
    def node(id: String): Node[Unit] =
      Node(id, statement, why, NodeKind.Claim, formula = Some(Lifted.thunk(() => formula, Source.text(formula))), ideaSection = idea,
        file = Source.here, at = Source.at)
    node(Source.nodeId)

  /** Every call `op(a, b, …)` meets `post(a, b, …, op(a, b, …))`: code attached to the operation is proven or checked
    * against it. On a flow's operation (`A => Flow[R]`), every run of `op(a, …)` from a world meets
    * `post(a, …, result, before, after)`, where `before(Model)` is a model's state before the run.
    */
  inline def contract[F](op: Param[F])(using s: Sig[F])(statement: String, why: String = "", idea: String = "")(
      inline post: s.Lam[Term[Boolean]]): Node[F] =
    def node(id: String): Node[F] =
      Node(id, statement, why, NodeKind.Contract, post = Some(Lifted.lambda(post, lambdaTypes(op), Source.text(post))), op = Some(op),
        ideaSection = idea, file = Source.here, at = Source.at)
    node(Source.nodeId)

  /** A contract written as a claim, `forall((a, b) => … op(a, b) …)`, with one operation applied to the forall's
    * variables in order: the same contract as `contract(op)(id, statement)((a, b, result) => …)`, `op(a, b)` read as
    * `result`.
    */
  transparent inline def contract(statement: String)(inline formula: Term[Boolean]): Node[?] =
    ${ ContractMacros.claimShaped('statement, 'formula) }

  @scala.annotation.publicInBinary private[frflow] def claimShaped[F](op: Param[F], id: String, statement: String,
      formula: Lifted[?], file: String, at: Int): Node[F] =
    Node(id, statement, "", NodeKind.Contract, post = Some(ClaimShaped.post(op, formula)), op = Some(op), file = file, at = at)

  /** What the outside (a database, the clock) is trusted to do on each call: code calling it is proven from it, its
    * adapter checked: `Node.assumption(fetch)(id, statement, why)((user, query, rows) => …)`.
    */
  def assumption[F](op: Param[F])(using s: Sig[F]): AssumptionOn[F, s.Lam[Term[Boolean]]] = AssumptionOn(op)

  /** What a boundary does, as its model says: `Node.assumption(db)(DatabaseModel)(id, statement, why)`. Trusted:
    * proven flows calling the boundary are proven from the model.
    */
  def assumption[T](boundary: Boundary[T]): ModelFor[T] = ModelFor(boundary)

  /** A flow's operation's inputs and its result's type (`(A, B) => Flow[R]` gives `[A, B]` and `R`). */
  private[frflow] def flowTypes(op: Param[?]): (List[LeanType[?]], LeanType[?]) = op.termType.shape match
    case Shape.FnOf(as, r) => r.shape match
      case Shape.FlowOf(x) => (as, x)
      case _               => throw IllegalArgumentException(s"FrFlow: ${op.name} is not a flow's operation (A => Flow[R])")
    case _ => throw IllegalArgumentException(s"FrFlow: ${op.name} is not a flow's operation (A => Flow[R])")

  /** A fact of the world, trusted; checked at run time where the terms it reads are bound, when it can be computed. */
  inline def assumption(statement: String, why: String, idea: String = "")(inline formula: Term[Boolean]): Node[Unit] =
    def node(id: String): Node[Unit] =
      Node(id, statement, why, NodeKind.Assumption, formula = Some(Lifted.thunk(() => formula, Source.text(formula))), ideaSection = idea,
        file = Source.here, at = Source.at)
    node(Source.nodeId)

  /** Fixes terms of the vocabulary (`User := of[UserId]`, `authorized := (u, p) => ...`): decided, not proven. */
  inline def definition(statement: String, why: String)(substs: Subst*): Node[Unit] =
    def node(id: String): Node[Unit] =
      Node(id, statement, why, NodeKind.Definition, substs = substs.toList, file = Source.here, at = Source.at)
    node(Source.nodeId)

  /** `rule(a, b)` holds for every pair a call exposes: every contract below `scope` that can expose one keeps it or is `exempt`. */
  inline def invariant[A, B](statement: String, why: String, scope: List[Node[?]] = Nil, idea: String = "")(
      inline rule: (Term[A], Term[B]) => Term[Boolean])(using a: LeanType[A], b: LeanType[B]): Node[(A, B) => Boolean] =
    def node(id: String): Node[(A, B) => Boolean] =
      Node(id, statement, why, NodeKind.Claim, rule = Some(Lifted.lambda(rule, List(a, b), Source.text(rule))), scope = scope,
        ideaSection = idea, file = Source.here, at = Source.at)
    node(Source.nodeId)

  /** An architecture choice or a convention, with no formal model; a change to the files it `governs` is noticed. */
  inline def design(statement: String, why: String, idea: String = "")(governs: String*): Node[Unit] =
    def node(id: String): Node[Unit] =
      Node(id, statement, why, NodeKind.Design, governs = governs.toList, ideaSection = idea, file = Source.here, at = Source.at)
    node(Source.nodeId)

  /** What a lambda over a call of the operation takes: its inputs and result; a flow's, then the worlds before and after. */
  private[frflow] def lambdaTypes(op: Param[?]): List[LeanType[?]] = op.termType.shape match
    case Shape.FnOf(as, r) => r.shape match
      case Shape.FlowOf(x) => as ++ List(x, summon[LeanType[World]], summon[LeanType[World]])
      case _               => as :+ r
    case _ => throw IllegalArgumentException(s"FrFlow: ${op.name} is not an operation (a function)")

  /** How many inputs the operation takes. */
  private[frflow] def arity(op: Param[?]): Int = op.termType.shape match
    case Shape.FnOf(as, _) => as.size
    case _                 => throw IllegalArgumentException(s"FrFlow: ${op.name} is not an operation (a function)")

  extension [T, S](n: Node[Modelled[T, S]])
    /** An outside system implementing the boundary (a database): its model stays assumed. It is checked against the
      * model on the examples of the flows calling it, and on generated runs of its operations from generated states.
      * `start` makes one holding a model's state, `read` reads its state back; both are compared as it holds a state
      * (stored and read back), so order it does not keep, such as rows a table returns sorted, is not compared.
      */
    inline def checkedAgainst[I <: T](inline start: S => I, inline read: I => S): Node[Modelled[T, S]] =
      n.withImpl(ModelImpl(start.asInstanceOf[Any => Any], read.asInstanceOf[Any => Any], outside = true, Source.text(start),
        Source.sourceFiles(start)))

    /** The project's own code implementing the boundary (an in-memory store, a cache): tested against the model, not
      * assumed. Generated runs of its operations, from generated states, must give what the model gives, and leave what
      * the model leaves (read back with `read`); a run that does not is shrunk and reported.
      */
    inline def implementedBy[I <: T](inline start: S => I, inline read: I => S): Node[Modelled[T, S]] =
      n.withImpl(ModelImpl(start.asInstanceOf[Any => Any], read.asInstanceOf[Any => Any], outside = false, Source.text(start),
        Source.sourceFiles(start)))

    private[frflow] def withImpl(i: ModelImpl): Node[Modelled[T, S]] = n.copy(modelOf = n.modelOf.map(m => m.copy(impls = m.impls :+ i)))

  extension [F](n: Node[F])
    /** What `service` checks on every call instead of the post: Lean proves the post implies it, so it refuses nothing allowed. */
    inline def checkedBy(using s: Sig[F])(inline check: s.Lam[Term[Boolean]]): Node[F] =
      n.copy(local = Some(Lifted.lambda(check, n.op.toList.flatMap(Node.lambdaTypes), Source.text(check))))

    /** How `service` checks this code's results where it runs, instead of the default for its kind: every call for code
      * Lean does not prove (it rests on tests, or is an outside system), none for code it proves. A decision: `show` says it.
      * `RunCheck.Sampled(100)` checks one call in a hundred, for a check that costs as much as the specification it states.
      */
    def checkedAtRunTime(check: RunCheck): Node[F] =
      check match
        case RunCheck.Sampled(k, _) => require(k >= 1, s"${n.id}: sample one call in 1 or more, not in $k")
        case _                      => ()
      n.copy(runCheck = Some(check))

    /** Keeps an invariant: its rule holds for each pair `view(inputs…, result)` lists (`result.map(r => (reader, r))`). */
    inline def keeps[X, Y](invariant: Node[(X, Y) => Boolean])(using s: Sig[F])(inline view: s.Lam[Term[List[(X, Y)]]]): Node[F] =
      require(invariant != null, s"${n.id} keeps an invariant declared after it: declare the invariant first")
      n.copy(kept = n.kept :+ Keep(invariant, Some(Lifted.lambda(view, n.op.toList.flatMap(Node.lambdaTypes), Source.text(view)))))

    /** Concrete cases, under the given parameter values: they fail when the contract or the code is not what was decided.
      * A call's (`allows(a, b, result, note)`), or a flow's run (`allows(a, before, result, after, note)`).
      */
    inline def examples(inline bindings: Binding*)(inline cases: Case[F]*): Node[F] =
      // Built in a method of its own (a file's top-level vals initialize in one JVM method of at most 64 KB).
      def exampleList(): List[Example] =
        cases.toList.map(c => Example(c.note, bindings.toList, Source.sources(bindings*), c.inputs, c.result, c.expected))
      n.copy(cases = n.cases ++ exampleList())

    /** Concrete cases where nothing is to be bound: `.examples(allows(…), forbids(…))`, as `.examples()(…)`. */
    inline def examples(inline cases: Case[F]*): Node[F] =
      def exampleList(): List[Example] = cases.toList.map(c => Example(c.note, Nil, Nil, c.inputs, c.result, c.expected))
      n.copy(cases = n.cases ++ exampleList())

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
            val onContract = ExampleRuns.verdict(Try {
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
            val onCode = code.map(c => ExampleRuns.verdict(c.flatMap(f => Try(returned(Fn.call(f, ins))))))
            (code.fold(built)(built.updated(e.bindings, _)), out :+ ExampleResult(e, onContract, onCode))
          }
        }._2.toList
      }

  // The IR is untyped: the builders gave the post, the check and the views the types of a call of the operation, so here a
  // call is its inputs (a flow's run: its inputs and the world before) and its result (a flow's: the result and the world after).
  extension (n: Node[?])
    private[frflow] def postFn: Option[(List[Any], Any) => Boolean] = n.post.map { p =>
      if n.isFlow then (ins: List[Any], r: Any) => r match
        // A run that failed: what the contract says of one (nothing changed, or its failure clause).
        case (Failed(e), after) => n.failure.exists(f => f.post.fold(after == ins.last)(fp =>
          Fn.call(fp.value, List(e, ins.last, after)).asInstanceOf[Boolean]))
        case (x, after) => Fn.call(p.value, ins.init ++ List(x, ins.last, after)).asInstanceOf[Boolean]
        case _          => false
      else (ins: List[Any], r: Any) => Fn.call(p.value, ins :+ r).asInstanceOf[Boolean]
    }
    def broken(inputs: List[Any], r: Any): Option[String] = n.kept.find(_.brokenBy(inputs, r)).map(_.invariant.id)

  extension [F](n: Node[F])
    /** `impl` (a Scala function of the operation's inputs) wrapped as `service` runs it: a function of the same inputs. */
    private[frflow] def enforce(impl: F, assumes: List[Assumption] = Nil, runCheck: RunCheck = RunCheck.EveryCall,
        report: Violation => Unit = Violation.log)(bindings: Binding*): F =
      // The cheap check when the contract gives one (Lean proves the post implies it), else the post.
      val (lifted, what) = (n.local, n.post) match
        case (Some(l), Some(_)) => (l, "its check")
        case (None, Some(p))    => (p, "the contract")
        case _                  => throw IllegalArgumentException(s"${n.id} is not a contract")
      val check = lifted.value
      val sampled = RunTimeChecks.chooser(runCheck)
      // What each assumption was last found to hold of: checked again when a value it reads changes.
      val held = AtomicReference(Map.empty[String, List[Any]])
      def same(xs: List[Any], ys: List[Any]) =
        xs.size == ys.size && xs.zip(ys).forall((p, q) => p.asInstanceOf[AnyRef] eq q.asInstanceOf[AnyRef])
      def fail(v: Violation): Nothing = { report(v); throw ContractViolation(v) }
      val all = bindings.toIndexedSeq
      val index = Bindings.index(all)
      Fn.of(n.op.map(Node.arity).getOrElse(0)) { ins =>
        // Each parameter is read once per call, and only if something reads it (a whole table a cheap check does
        // not read is never loaded): the implementation and the check see the same values.
        val cells = Bindings.call(index, all)
        Bindings.in(cells) {
          val r = Fn.call(impl.asInstanceOf[AnyRef], ins)
          if sampled() then
            if !Fn.call(check, ins :+ r).asInstanceOf[Boolean] then fail(Violation(n.id, what, ins, Some(r)))
            n.broken(ins, r).foreach(i => fail(Violation(n.id, s"the invariant $i", ins, Some(r))))
          // The values it ran with are checked whatever the code: they are about the world, and cheap (once per change).
          assumes.filter(x => x.reads.forall(cells.loaded)).foreach { x =>
            val vs = x.reads.toList.sorted.flatMap(cells.value)
            if !held.get.get(x.what).exists(same(_, vs)) then
              if !x.holds() then fail(Violation(n.id, s"the assumption ${x.what}", ins, None))
              held.updateAndGet(_.updated(x.what, vs))
          }
          r
        }
      }.asInstanceOf[F]

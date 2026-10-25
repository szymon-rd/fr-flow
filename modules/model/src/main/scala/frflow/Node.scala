package frflow

import frflow.protocol.{NodeKind, RunCheck}

/** How a node stands to an invariant: kept, through a view of each call, or exempt. */
final case class Keep(invariant: Node[?], view: Option[Lifted[?]], exempt: String = ""):
  def describe: String = view.fold(s"${invariant.id}: exempt, because ${exempt}")(v => s"${invariant.id}: ${v.source}")

  // The casts are where the untyped IR meets the values: `keeps` built the view over the call and the rule over a pair.
  private[frflow] def brokenBy(inputs: List[Any], r: Any): Boolean =
    view.exists { v =>
      invariant.rule.exists { rl =>
        val rule = rl.value.asInstanceOf[(Any, Any) => Boolean]
        Fn.call(v.value, inputs :+ r).asInstanceOf[List[(Any, Any)]].exists((x, y) => !rule(x, y))
      }
    }

/** One statement in the developer's domain words, decided by them and proven in Lean from its parts (the nodes
  * that name it `under`). `M` is the operation's type, so examples and checks are typed.
  */
final class Node[M] @scala.annotation.publicInBinary private[frflow] (val id: String, val statement: String, val why: String,
    val kind: NodeKind, val declaredParents: List[Node[?]] = Nil, val formula: Option[Lifted[?]] = None,
    val post: Option[Lifted[?]] = None, val op: Option[Param[?]] = None, val rule: Option[Lifted[?]] = None,
    val substs: List[Subst] = Nil, val cases: List[Example] = Nil, val governs: List[String] = Nil, val kept: List[Keep] = Nil,
    val scope: List[Node[?]] = Nil, val ideaSection: String = "", val file: String = "", val expected: List[(String, Lifted[?])] = Nil,
    val at: Int = -1, val local: Option[Lifted[?]] = None, val replaced: Option[Node[?]] = None,
    val modelOf: Option[ModelOf] = None, val runCheck: Option[RunCheck] = None):
  def parents: List[Node[?]] = (declaredParents ++ kept.collect { case Keep(i, Some(_), _) => i }).distinctBy(System.identityHashCode)
  def isInvariant: Boolean = rule.isDefined
  def shownKind: String = kind.shown(isInvariant)
  /** A contract on a flow: its operation runs from a world (`A => Flow[R]`), its post relates the worlds before and after. */
  def isFlow: Boolean = op.exists(o => o.termType.shape match { case Shape.FnOf(_, r) => r.shape.isInstanceOf[Shape.FlowOf]; case _ => false })
  def defines: List[String] = substs.map(_.name)
  def referenced: List[Lifted[?]] = formula.toList ++ post.toList ++ rule.toList ++ local.toList ++ substs.flatMap(_.term) ++
    kept.flatMap(_.view) ++ expected.map(_._2)

  // `require` in the builders: a node built from one declared after it gets `null` (Scala initializes vals in
  // order), and failing as the model loads, naming the node, is what the developer can act on.

  /** A part of each of `ps`: with its co-parts, it refines each. */
  def under(ps: Node[?]*): Node[M] =
    require(ps.forall(_ != null), s"$id is under a node declared after it: declare the parent first")
    require(kind != NodeKind.Definition, s"$id: a definition has no parents; the nodes that use its terms rest on it")
    copy(declaredParents = declaredParents ++ ps)

  /** An alternative to `other`: accepting one rejects the other. */
  def replaces(other: Node[?]): Node[M] =
    require(other != null, s"$id replaces a node declared after it: declare it first")
    copy(replaced = Some(other))

  /** A consequence the developer expects, which Lean proves from the claim: "Acme never sees Globex's contact". */
  inline def expects(statement: String)(inline consequence: Term[Boolean]): Node[M] =
    copy(expected = expected :+ (statement -> Lifted.thunk(() => consequence, Source.text(consequence))))

  private[frflow] def copy(declaredParents: List[Node[?]] = declaredParents, cases: List[Example] = cases, kept: List[Keep] = kept,
      expected: List[(String, Lifted[?])] = expected, local: Option[Lifted[?]] = local, replaced: Option[Node[?]] = replaced,
      modelOf: Option[ModelOf] = modelOf, runCheck: Option[RunCheck] = runCheck): Node[M] =
    Node(id, statement, why, kind, declaredParents, formula, post, op, rule, substs, cases, governs, kept, scope, ideaSection,
      file, expected, at, local, replaced, modelOf, runCheck)

  /** The invariant does not apply to this contract or design decision, for the reason given (which the developer reads). */
  def exempt(invariant: Node[?], because: String): Node[M] =
    require(invariant != null, s"$id is exempt from an invariant declared after it: declare the invariant first")
    copy(kept = kept :+ Keep(invariant, None, because))
  override def toString: String = id

object Node:
  // Each is built in a method of its own: a file's top-level vals initialize in one JVM method (at most 64 KB).

  /** With no parents, the root: the idea's purpose, stated as *exactly*, so that doing nothing does not meet it. */
  inline def claim(id: String, statement: String, why: String, idea: String = "")(inline formula: Term[Boolean]): Node[Unit] =
    def node(): Node[Unit] =
      Node(id, statement, why, NodeKind.Claim, formula = Some(Lifted.thunk(() => formula, Source.text(formula))), ideaSection = idea,
        file = Source.here, at = Source.at)
    node()

  /** Every call `op(a, b, …)` meets `post(a, b, …, op(a, b, …))`: code attached to the operation is proven or checked
    * against it. On a flow's operation (`A => Flow[R]`), every run of `op(a, …)` from a world meets
    * `post(a, …, result, before, after)`, where `before(Model)` is a model's state before the run.
    */
  inline def contract[F](op: Param[F])(using s: Sig[F])(id: String, statement: String, why: String, idea: String = "")(
      inline post: s.Lam[Term[Boolean]]): Node[F] =
    def node(): Node[F] =
      Node(id, statement, why, NodeKind.Contract, post = Some(Lifted.lambda(post, lambdaTypes(op), Source.text(post))), op = Some(op),
        ideaSection = idea, file = Source.here, at = Source.at)
    node()

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
  inline def assumption(id: String, statement: String, why: String, idea: String = "")(inline formula: Term[Boolean]): Node[Unit] =
    def node(): Node[Unit] =
      Node(id, statement, why, NodeKind.Assumption, formula = Some(Lifted.thunk(() => formula, Source.text(formula))), ideaSection = idea,
        file = Source.here, at = Source.at)
    node()

  /** Fixes terms of the vocabulary (`User := of[UserId]`, `authorized := (u, p) => ...`): decided, not proven. */
  inline def definition(id: String, statement: String, why: String)(substs: Subst*): Node[Unit] =
    def node(): Node[Unit] =
      Node(id, statement, why, NodeKind.Definition, substs = substs.toList, file = Source.here, at = Source.at)
    node()

  /** `rule(a, b)` holds for every pair a call exposes: every contract below `scope` that can expose one keeps it or is `exempt`. */
  inline def invariant[A, B](id: String, statement: String, why: String, scope: List[Node[?]] = Nil, idea: String = "")(
      inline rule: (Term[A], Term[B]) => Term[Boolean])(using a: LeanType[A], b: LeanType[B]): Node[(A, B) => Boolean] =
    def node(): Node[(A, B) => Boolean] =
      Node(id, statement, why, NodeKind.Claim, rule = Some(Lifted.lambda(rule, List(a, b), Source.text(rule))), scope = scope,
        ideaSection = idea, file = Source.here, at = Source.at)
    node()

  /** An architecture choice or a convention, with no formal model; a change to the files it `governs` is noticed. */
  inline def design(id: String, statement: String, why: String, idea: String = "")(governs: String*): Node[Unit] =
    def node(): Node[Unit] =
      Node(id, statement, why, NodeKind.Design, governs = governs.toList, ideaSection = idea, file = Source.here, at = Source.at)
    node()

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

/** A boundary and the model it is decided to behave as, with the implementations of the boundary checked against it. */
final case class ModelOf(boundary: Boundary[?], model: StateModel[?], impls: List[ModelImpl] = Nil)

/** An implementation of a boundary, started in a model's state (`start`) and read back (`read`): an outside system
  * (`outside`: a database; its model stays assumed) or code of the project's own (tested against the model). `source`
  * is how it is started, as written; `files`, the project files that expression refers to (the model's file last).
  */
final case class ModelImpl(start: Any => Any, read: Any => Any, outside: Boolean, source: String, files: List[String]):
  def sources: List[String] = files.dropRight(1)

/** A boundary's model, decided: `T` is the boundary's trait, `S` the model's state. */
final class Modelled[T, S] private ()

/** `Node.assumption(db)(DatabaseModel)(id, statement, why, idea)`. */
final class ModelFor[T](boundary: Boundary[T]):
  def apply[S](model: T & StateModel[S]): ModelNode[T, S] = ModelNode(ModelOf(boundary, model))
final class ModelNode[T, S](m: ModelOf):
  inline def apply(id: String, statement: String, why: String, idea: String = ""): Node[Modelled[T, S]] =
    def node(): Node[Modelled[T, S]] =
      Node(id, statement, why, NodeKind.Assumption, ideaSection = idea, file = Source.here, at = Source.at, modelOf = Some(m))
    node()

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

/** `Node.assumption(op)(id, statement, why, idea)(post)`: a step of its own, so that both assumptions default `idea`; `P` is
  * the post's lambda over a call of `op` (`Sig`).
  */
final class AssumptionOn[F, P <: AnyRef] private[frflow] (val op: Param[F]):
  inline def apply(id: String, statement: String, why: String, idea: String = "")(inline post: P): Node[F] =
    def node(): Node[F] =
      Node(id, statement, why, NodeKind.Assumption, post = Some(Lifted.lambda(post, Node.lambdaTypes(op), Source.text(post))), op = Some(op),
        ideaSection = idea, file = Source.here, at = Source.at)
    node()

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
    * A call's (`expect(a, b, result, note)`), or a flow's run (`expect(a, before, result, after, note)`).
    */
  inline def examples(inline bindings: Binding*)(inline cases: Case[F]*): Node[F] =
    // Built in a method of its own (a file's top-level vals initialize in one JVM method of at most 64 KB).
    def exampleList(): List[Example] =
      cases.toList.map(c => Example(c.note, bindings.toList, Source.sources(bindings*), c.inputs, c.result, c.expected))
    n.copy(cases = n.cases ++ exampleList())

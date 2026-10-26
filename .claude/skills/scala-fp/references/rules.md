# Rules with examples

Each rule from `SKILL.md` has a short bad and good example in Scala 3, shaped
like FrFlow's code where possible, and the source it comes from (expanded in
`sources.md`). The good examples show a shape. A change to a core type still
goes through `refactoring.md`, where the owner approves the design.

## Domain modelling

### D1 One concept per type

`Node` has 24 constructor fields for six kinds of node. Which fields are set
depends on `kind`, and only the builders know which.

```scala
// bad
final class Node[M](val id: String, val statement: String, val why: String, val kind: NodeKind,
    val formula: Option[Lifted[?]] = None, val post: Option[Lifted[?]] = None, val op: Option[Param[?]] = None,
    val rule: Option[Lifted[?]] = None, val substs: List[Subst] = Nil, val governs: List[String] = Nil, /* 14 more */)
```

```scala
// good: each case holds what that kind of node is
enum Node:
  case Claim(about: Statement, formula: Lifted[Boolean])
  case Invariant(about: Statement, rule: Rule, scope: List[NodeId])
  case Contract(about: Statement, op: Operation, post: Post, check: Option[Check])
  case Assumption(about: Statement, trusted: Trusted)
  case Definition(about: Statement, terms: NonEmptyList[Subst])
  case Design(about: Statement, governs: NonEmptyList[RelPath])
```

Source: Wlaschin, "Designing with types: making illegal states unrepresentable";
King, "Parse, don't validate"; Effective Scala, "Case classes as algebraic data
types".

### D2 Make illegal states unrepresentable

```scala
// bad: the type allows a definition with parents, and a builder rejects it at run time
def under(ps: Node[?]*): Node[M] =
  require(kind != NodeKind.Definition, s"$id: a definition has no parents")
  copy(declaredParents = declaredParents ++ ps)
```

```scala
// good: only the cases that can have parents have `under`
final case class Refines(node: NodeId, parents: NonEmptyList[NodeId])
extension (c: Node.Claim | Node.Contract | Node.Invariant)
  def under(p: NodeId, ps: NodeId*): Refines = Refines(c.about.id, NonEmptyList(p, ps.toList))
```

Source: Wlaschin (the phrase is Yaron Minsky's); King, "Use a data structure
that makes illegal states unrepresentable".

### D3 Store each fact once

```scala
// bad: whether a node is an invariant is stored twice, as `kind` (Claim) plus `rule.isDefined`
def isInvariant: Boolean = rule.isDefined
def shownKind: String = kind.shown(isInvariant)
```

```scala
// good: the case is the fact
node match
  case _: Node.Invariant => "invariant"
  case _: Node.Claim     => "claim"
```

Source: King, "Avoid denormalized representations of data".

### D4 Opaque types for ids, paths, hashes, quantities

```scala
// bad
val governs: List[String] = Nil   // file paths
val file: String = ""             // the file the node is written in
```

```scala
// good
opaque type RelPath = String
object RelPath:
  def parse(s: String): Either[PathError, RelPath] =
    val p = java.nio.file.Path.of(s).normalize
    Either.cond(!p.isAbsolute && !p.startsWith(".."), p.toString, PathError.OutsideRoot(s))
  extension (p: RelPath) def under(root: java.nio.file.Path): java.nio.file.Path = root.resolve(p)

final case class SourcePos(file: RelPath, line: Int)
```

`NodeId`, `Hash`, `KeyId` and `Fingerprint` in `protocol` already follow this rule.

Source: Scala 3 reference, "Opaque type aliases"; Li Haoyi, "Practical Type
Safety" (box integer ids, avoid strings in favour of structured data); Volpe,
*Practical FP in Scala* (newtypes).

### D5 No stringly typed data, no sentinels

```scala
// bad
val ideaSection: String = ""   // "" means none
val at: Int = -1               // -1 means not from a source file
```

```scala
// good
val idea: Option[IdeaSection]
val at: Option[SourcePos]      // absent for nodes built by code, which the domain allows
```

Source: Li Haoyi, "Practical Type Safety" (avoid string flags, avoid integer
enums); King.

### D6 Parse, don't validate

```scala
// bad: every user of the list checks it again, or forgets to
def governed(files: List[String]): List[String] = files.filter(f => !f.startsWith("/"))
```

```scala
// good: parse once where the strings enter, then pass the parsed type
def design(about: Statement)(governs: String*): Either[ModelError, Node.Design] =
  governs.toList.traverse(RelPath.parse).leftMap(ModelError.BadPath(about.id, _))
    .flatMap(ps => NonEmptyList.fromList(ps).toRight(ModelError.GovernsNothing(about.id)))
    .map(Node.Design(about, _))
```

Source: King, "Parse, don't validate" (push the burden of proof upward, to the
boundary); Volpe (refined types and smart constructors).

### D7 Option means absent in the domain; no field defaults

```scala
// bad: `post`, `op`, `failure` and `runCheck` are Some exactly when kind == Contract
val post: Option[Lifted[?]] = None, val op: Option[Param[?]] = None, val failure: Option[FailureClause] = None
```

```scala
// good: a contract always has an operation and a post; a failure clause is genuinely optional
case Contract(about: Statement, op: Operation, post: Post, onFailure: Option[FailureClause])
```

Source: Wlaschin's `Contact` example (two options that encode "email or postal
address" become a union); King, "Let your datatypes inform your code".

### D8 Enums instead of Booleans

```scala
// bad
val openAbove: Boolean = false
final case class SnapNode(..., rule: Boolean = false, leaf: Boolean = false, ...)
```

```scala
// good
enum Fixes:
  case WordsLeftOpenAbove, NothingAbove
```

Source: King ("avoid the temptation to just stick a Bool in a record");
VirtusLab, domain modelling.

### D9 Lifecycle stages as types

```scala
// bad: one type whose options fill in as checks run
final case class SnapNode(..., status: Option[CheckStatus] = None, tested: Option[TestReport] = None,
    proof: Option[ProofFile] = None, runtime: Option[RunTime] = None)
```

```scala
// good: what a node is, and what a check found about it, are separate values
final case class Checked(node: NodeId, status: CheckStatus, proof: Option[ProofFile])
final case class Snapshot(nodes: List[SnapNode], checks: Map[NodeId, Checked], tests: Map[NodeId, TestReport])
```

Source: Wlaschin, "Designing with types: making state explicit".

### D10 Collections that state the invariant

```scala
// bad: identity hash as a key means the nodes have no usable id here
def parents: List[Node[?]] = (declaredParents ++ kept.collect { case Keep(i, Some(_), _) => i })
  .distinctBy(System.identityHashCode)
```

```scala
// good
def parents(id: NodeId): Set[NodeId] = refines.getOrElse(id, Set.empty) ++ kept.getOrElse(id, Set.empty)
```

Source: King (`NonEmpty`, `Map` instead of a list checked for duplicates);
cats `NonEmptyList`.

### D11 No `Any` or casts in domain signatures

```scala
// bad: casts spread over the domain type's file
private[frflow] def postFn: Option[(List[Any], Any) => Boolean] =
  n.post.map(p => (ins, r) => Fn.call(p.value, ins :+ r).asInstanceOf[Boolean])
```

```scala
// good: the untyped IR is one module, entered through typed constructors; casts stay inside it
object Untyped:
  /** The builders gave `post` the type of a call of `op`, so this cast cannot fail. */
  def predicate(post: Post): (List[Any], Any) => Boolean = (ins, r) => Fn.call(post.value, ins :+ r).asInstanceOf[Boolean]
```

Source: Effective Scala, "Types and generics" (the type system is there to
detect errors); King ("treat those situations like the radioactive substance
they are").

### D12 Data is a case class or enum

```scala
// bad: a class with a private constructor and a hand-written ten-parameter `copy`
final class Node[M] private[frflow] (val id: String, ...):
  private[frflow] def copy(declaredParents: List[Node[?]] = declaredParents, cases: List[Example] = cases, ...): Node[M]
```

```scala
// good
final case class Statement(id: NodeId, text: String, why: String, idea: Option[IdeaSection], at: Option[SourcePos])
```

Source: Li Haoyi, "Designing Datatypes" (transparent case classes for data,
opaque classes only for types with internal invariants).

## Data and behaviour

### B1 Core types hold data and their essential operations

```scala
// bad: the domain type knows how to compute Lean types for one printer
private[frflow] def opType: Option[LeanType[?]] = op.map(o => (o.termType.shape, failure) match ...)
```

```scala
// good: the operation's own type is essential; how Lean renders a failing flow belongs to the Lean module
final case class Operation(name: String, signature: Signature)   // in node
object FlowTypes:                                                 // in lean
  def outcome(op: Operation, failure: Option[FailureClause]): LeanType[?] = ...
```

Source: Ghosh, *Functional and Reactive Domain Modeling* (algebra, then
interpreters); Chiusano and Bjarnason, *FPiS* part 2.

### B2 Interpreters outside the type

```scala
// bad: Node.scala defines the node, runs its examples (checkExamples) and wraps code with run-time checks (enforce)
extension (n: Node[?]) private[frflow] def checkExamples(impl: Option[() => Any], ...): List[ExampleResult] = ...
extension [F](n: Node[F]) private[frflow] def enforce(impl: F, ...)(bindings: Binding*): F = ...
```

```scala
// good: one interpreter per package, each depending on node
package frflow.example: object ExampleCheck { def results(c: Node.Contract, impl: Option[Impl]): List[ExampleResult] }
package frflow.runtime: object Enforce     { def wrap[F](c: Node.Contract, impl: F, plan: RunPlan): F }
```

Source: Ghosh; Volpe (algebras, interpreters, programs); Bernhardt.

### B3 Dependencies point inward

```scala
// bad: node imports what runs it
package frflow.node
import frflow.example.ExampleRuns
import frflow.runtime.RunTimeChecks
import java.util.concurrent.atomic.AtomicReference
```

```scala
// good: node imports only the vocabulary it is made of
package frflow.node
import frflow.protocol.NodeId
import frflow.vocabulary.{Lifted, Subst}
```

Check with `grep -rn "^import frflow\.\(runtime\|example\|testing\)" modules/model/src/main/scala/frflow/{node,kb,term,types,vocabulary}`.

Source: Bernhardt, "Boundaries"; Volpe (layering).

### B4 Algebra first

```scala
// bad: the type is written first, and its operations are added when a caller needs one
```

```scala
// good: write the operations and their laws before the representation
trait Refinement:
  /** The nodes `n` rests on. Law: every invariant `n` keeps is among them. */
  def parents(n: NodeId): Set[NodeId]
  /** Law: `replaces` is irreflexive, and a node replaces at most one other. */
  def replaced(n: NodeId): Option[NodeId]
```

Source: Chiusano and Bjarnason, *FPiS* 2nd ed., chapters 7 to 9 (algebraic
design: start from the operations and laws); Ghosh (algebra of the API).

### B5 How something runs is not part of the concept

```scala
// bad: a deployment's sampling rate stored on the statement the developer decided
n.copy(runCheck = Some(RunCheck.Sampled(100)))
```

```scala
// good: the wiring says how each contract is checked where it runs
final case class RunPlan(checks: Map[NodeId, RunCheck], report: Violation => IO[Unit])
```

Source: Bernhardt (values at the boundary, the shell decides how to run);
Wlaschin, DMMF (workflows take their dependencies as parameters).

## Functions

### F1 One job per function

`enforce` chooses the check, builds the sampler, caches what each assumption
was last checked against, binds parameters, runs the code, checks the result,
reports and throws: about eight jobs in 30 lines.

```scala
// good: an orchestration of named steps, each testable alone
def wrap[F](c: Node.Contract, impl: F, plan: RunPlan): F =
  val check = Check.of(c)                     // pure: the cheap check if given, else the post
  val watch = AssumptionWatch(plan.assumes)   // what each assumption was last checked against
  Fn.of(c.op.arity)(ins => Call.run(check, watch, plan, impl, ins))
```

Source: Effective Scala ("think always of the reader"); VirtusLab (one concern
per function).

### F2 Within the size budgets

```scala
// bad: a 99-line `compile` with nested matches and local defs
```

```scala
// good: a total match whose cases delegate (the one allowed exception to the line budget)
def compile(t: Term[?]): Compiled = t match
  case Term.Lit(v)       => Compiled.lit(v)
  case Term.App(f, args) => app(f, args)
  case Term.Lam(ps, b)   => lam(ps, b)
```

Source: section 3 of `SKILL.md`; scalastyle defaults (50 lines, 8 parameters,
800-line files) as an upper reference.

### F3 Total functions

```scala
// bad
case _ => throw IllegalArgumentException(s"${n.id} is not a contract")
```

```scala
// good: take the case you need, so there is nothing to reject
def wrap[F](c: Node.Contract, impl: F, plan: RunPlan): F
```

Source: King, "Turning partial functions total".

### F4 Names

```scala
// bad
def go(xs: List[Node[?]]): List[String] = ...
def process(n: Node[?]): Unit = ...
```

```scala
// good
def unprovenBelow(root: NodeId): List[NodeId] = ...
```

Source: Li Haoyi, "Conciseness and names" (a name shows the reader something
they do not already know and want to know; length follows scope).

### F5 Explicit return types on non-local members

```scala
// bad
def of(v: View) = of(v, Waiting.forDeveloper(v.annotated))
```

```scala
// good
def of(v: View): Overview = of(v, Waiting.forDeveloper(v.annotated))
```

Source: Scala style guide, "Declarations" ("documentation checked by the
compiler"); Effective Scala, "Return type annotations".

### F6 Default arguments

```scala
// bad: a hidden effect and a hidden policy as defaults on an internal function
def enforce(impl: F, assumes: List[Assumption] = Nil, runCheck: RunCheck = RunCheck.EveryCall,
    report: Violation => Unit = Violation.log)(bindings: Binding*): F
```

```scala
// good: internal code passes everything; a published entry point may default an optional setting
def wrap[F](c: Node.Contract, impl: F, plan: RunPlan): F
def service[F](c: Contract[F], impl: F, check: RunCheck = RunCheck.EveryCall): Service[F]   // DSL entry point
```

Source: Effective Scala, "Dependency injection"; VirtusLab (lawful APIs); Li
Haoyi ranks default arguments as a low-power form of dependency injection,
which is why they stay allowed on published entry points.

### F7 Take a function when one method is used

```scala
// bad
def run(reporter: Reporter): Unit = reporter.report(v)
```

```scala
// good
def run(report: Violation => IO[Unit]): IO[Unit] = report(v)
```

Source: Li Haoyi, "Principle of Least Power" (published interfaces); Effective
Scala (factories as functions).

### F8 `require` only for FrFlow bugs

```scala
// bad: a mistake in the developer's model reported by an exception from a builder
require(kind == NodeKind.Contract, s"$id: only a contract fixes a word left open above")
```

```scala
// good: the method exists only on Contract (S2); what types cannot express is collected
def validate(kb: KnowledgeBase): ValidatedNec[ModelError, KnowledgeBase]
// and a FrFlow bug may still be asserted
assert(index.size == all.size, "Bindings.index dropped a parameter")
```

Source: Effective Scala, "`require` and `assert`" (executable documentation
where types cannot express the invariant); VirtusLab (`Either` instead of
`require` for recoverable failures); King.

### F9 No exceptions for control flow in the core

```scala
// bad
def flowTypes(op: Param[?]): (List[LeanType[?]], LeanType[?]) = op.termType.shape match
  case Shape.FnOf(as, r) => ...
  case _ => throw IllegalArgumentException(s"FrFlow: ${op.name} is not a flow's operation (A => Flow[R])")
```

```scala
// good: a flow's operation is its own type, built once by the DSL
final case class FlowOp(name: String, inputs: List[LeanType[?]], result: LeanType[?])
```

Source: Effective Scala, "Error handling" (no exceptions for errors the
programmer must handle; `NonFatal` when catching).

### F10 `var` only inside a method

```scala
// bad
final class FaultPlan(faults: List[Boolean]):
  private val left = AtomicReference(faults)
  private[frflow] def next(): Boolean = left.getAndUpdate(_.drop(1)).headOption.contains(true)
```

```scala
// good: the plan is a value and the state is threaded through the run (or held in a Ref by the IO interpreter)
final case class FaultPlan(faults: List[Fault]):
  def next: (Option[Fault], FaultPlan) = (faults.headOption, FaultPlan(faults.drop(1)))
```

Source: Li Haoyi, "Principle of Least Power" (immutability; mutation scoped as
narrowly as possible); VirtusLab (no class-level `var`).

## Effects

### E1 Pure core

```scala
// bad: the knowledge base, a core aggregate, imports cats.effect and the runtime wiring
package frflow.kb
import cats.effect.IO
import frflow.runtime.Wiring
```

```scala
// good: the core is values and functions; the runtime module takes a KnowledgeBase
package frflow.runtime
def wire(kb: KnowledgeBase, impls: Implementations): Resource[IO, Running]
```

Source: Bernhardt ("Functional core, imperative shell"); *FPiS* chapter 13
("inside every function with side effects is a pure function waiting to get
out"); De Goes ("minimize effectful code").

### E2 Read inputs once, then call the core

```scala
// good, as in check.Inputs.read: all reads in parallel, once, then pure code
(Disk.read(idea), ledger, KeyStore.projectKeys(dir), checks(file), IO.realTimeInstant).parMapN(Inputs(_, _, _, _, _))
  .map(Verdict.of(kb, _))
```

```scala
// bad: the pure function reaches for the file system itself
def verdict(kb: KnowledgeBase): Verdict = Verdict(kb, Files.readString(Path.of(kb.idea)))
```

Source: Bernhardt; cats-effect, "Concepts" (effects are descriptions; wrap side
effects).

### E3 Every side effect in IO

```scala
// bad
def save(f: Path, s: String): IO[Unit] = { Files.writeString(f, s); IO.unit }
```

```scala
// good: blocking file I/O on the blocking pool
def save(f: Path, s: String): IO[Unit] = IO.blocking(Files.writeString(f, s)).void
```

Source: cats-effect, "Concepts" (side effects inside `IO(...)`, `IO.blocking`,
`IO.async`); "Thread model".

### E4 Resource for anything released

```scala
// bad: a process that is never destroyed when the fiber is cancelled
def lean(cmd: List[String]): IO[String] = IO.blocking(java.lang.ProcessBuilder(cmd*).start()).flatMap(read)
```

```scala
// good, as in check/process/Run: fs2's spawn is a Resource, so the process ends with `use`
ProcessBuilder(command, args).withWorkingDirectory(dir).spawn[IO].use(p => collect(p))
// and for a Java resource without one
Resource.make(IO.blocking(java.lang.ProcessBuilder(cmd*).start()))(p => IO.blocking(p.destroy()))
```

Source: cats-effect, "Resource".

### E5 Ref in IO code; AtomicReference only in synchronous wrappers, with a reason

```scala
// bad: IO code holding state in an AtomicReference
final class Sessions(private val open: AtomicReference[Map[SessionId, Session]])
```

```scala
// good
final class Sessions private (open: Ref[IO, Map[SessionId, Session]])
object Sessions:
  def make: IO[Sessions] = Ref.of[IO, Map[SessionId, Session]](Map.empty).map(Sessions(_))
```

Allowed with a comment: the function `service` returns is called synchronously
by the user's program, outside `IO`, so its per-wrapper cache is an
`AtomicReference` local to that wrapper.

Source: cats-effect, "Ref" (a purely functional wrapper over an
`AtomicReference`); VirtusLab.

### E6 `unsafeRun*` only at the entry point

```scala
// bad: deep inside the example runner
Flows.run[IO](steps, env, impls, bindings, Some(pause)).attempt.unsafeRunSync()
```

```scala
// good: one bridge, named and documented, that the synchronous API goes through
object RunNow:
  /** Runs a flow for a caller that is not in IO (the examples run as the model loads). */
  def run[A](io: IO[A])(using rt: IORuntime): Either[Throwable, A] = io.attempt.unsafeRunSync()
```

Source: cats-effect FAQ and `IOApp` documentation.

### E7 Clock, randomness and ids passed in

```scala
// bad
def sign(d: Decision): Signed = Signed(d, Instant.now())
```

```scala
// good
def sign(d: Decision, at: Instant): Signed = Signed(d, at)   // caller reads IO.realTimeInstant once
```

Source: VirtusLab, "Lawful APIs".

### E8 Concrete IO; F[_] only with two interpreters and laws

```scala
// bad: effect polymorphism with one interpreter, and Sync, which can capture any side effect
def check[F[_]: Sync](kb: KnowledgeBase): F[Verdict]
```

```scala
// good
def check(kb: KnowledgeBase): IO[Verdict]
// F[_] stays where it earns its place: user flows, interpreted over models and over real boundaries
def run[F[_]: Monad](steps: Steps, env: Env[F]): F[Outcome]
```

Source: De Goes, "The false hope of managing effects with tagless-final in
Scala" (premature indirection, `Sync` bloat; recommends a concrete effect for
applications); Volpe and the cats-effect tutorial (polymorphic code); Odersky,
"Lean Scala". See `sources.md`.

## Errors

### R1 Error ADTs per module

```scala
// bad
def accept(id: NodeId): IO[Either[String, Decision]]
```

```scala
// good
enum DecideError:
  case NotWaiting(id: NodeId, state: ReviewState)
  case Unsigned(id: NodeId)
  case StaleHash(id: NodeId, decided: Hash, now: Hash)
def accept(id: NodeId): IO[Either[DecideError, Decision]]
```

Source: Effective Scala, "Error handling"; VirtusLab (typed error hierarchies);
Volpe (error ADTs).

### R2 Either in pure code, IO for unhandled failures

```scala
// bad: a pure decision throws
def decide(r: Review): Decision = if r.hash != current then throw StaleHash(...) else ...
```

```scala
// good
def decide(r: Review, current: Hash): Either[DecideError, Decision]
```

Source: Effective Scala; cats, "Either".

### R3 Accumulate independent errors

```scala
// bad: the developer fixes one problem per run
for
  _ <- uniqueIds(kb)
  _ <- parentsDeclared(kb)
yield kb
```

```scala
// good
(uniqueIds(kb), parentsDeclared(kb), pathsExist(kb)).mapN((_, _, _) => kb)   // ValidatedNec[ModelError, _]
```

Source: cats, "Validated".

### R4 Convert at the boundary, render at the edge

```scala
// bad: the ledger builds CLI text
Left(s"${Colors.red("refused")}: $id is not waiting")
```

```scala
// good: the ledger returns DecideError; api maps it into FrFlowError; cli and web render it
def accept(id: NodeId): IO[Either[FrFlowError, Decision]] = ledger.accept(id).map(_.leftMap(FrFlowError.Decide(_)))
```

Source: Volpe (error handling per layer); Effective Scala.

## Type classes and givens

### T1 Type classes for canonical, generic operations

```scala
// bad: a type class with one use, standing in for a parameter
trait Reporter[A]: def report(a: A): Unit
def enforce[A: Reporter](...)
```

```scala
// good
given LeanType[NodeId] = LeanType.string.as[NodeId]   // one canonical instance per type
def wrap(..., report: Violation => IO[Unit])          // a plain parameter for a policy
```

Source: Scala 3 reference, "Given instances" ("canonical values"); Effective
Scala, "Implicits".

### T2 Coherence

```scala
// bad: an instance in an unrelated object, imported in some files and not others
object JsonStuff:
  given Codec[NodeId] = ...
```

```scala
// good
opaque type NodeId = String
object NodeId:
  given Codec[NodeId] = Codec.from(Decoder.decodeString, Encoder.encodeString)
```

Source: Scala 3 reference (implicit scope); cats guidelines (instance placement
and priority).

### T3 Implicit conversions only for DSL literal lifting

```scala
// bad: a conversion that hides an access
given ops[T]: Conversion[Boundary[T], T] = _.ops
```

```scala
// good: lifting literals into terms, all in one file
given int: Conversion[Int, Term[BigInt]] = i => Term.lit(BigInt(i))
// and an explicit accessor
db.ops.fetch(user)
```

Source: Scala 3 reference, "Contextual abstractions" (most applications of
implicit conversions are of dubious value); Odersky, "Lean Scala" (use
conversions and macros only when simpler means are not enough).

### T4 `using` for context, parameters for dependencies

```scala
// bad
def accept(id: NodeId)(using store: Store, keys: KeyStore, clock: Clock): IO[Decision]
```

```scala
// good
final class Decide(store: Store, keys: KeyStore):
  def accept(id: NodeId, at: Instant): IO[Either[DecideError, Decision]]
def contract[F](op: Param[F])(using s: Sig[F]): ...   // a typing witness is context
```

Source: Scala 3 reference, "Using clauses"; Effective Scala, "Dependency
injection".

### T5 Extension methods for opaque APIs and syntax

```scala
// bad: interpreters attached to Node through extensions in Node.scala
extension (n: Node[?]) private[frflow] def postFn: Option[(List[Any], Any) => Boolean]
```

```scala
// good
opaque type Hash = String
object Hash:
  extension (h: Hash) def short: String = h.take(8)
```

Source: Scala 3 reference, "Opaque type aliases" ("extension methods define
opaque types' public APIs").

### T6 Codecs on DTOs only

```scala
// bad
enum Node derives Codec.AsObject
```

```scala
// good
final case class SnapNode(...) derives Codec.AsObject   // in protocol
object SnapNode:
  def of(n: Node, found: Checked): SnapNode = ...         // in check/analysis, which sees both
```

Source: Volpe (domain types separate from request and response types).

## Modules and packages

### M1 A written dependency graph, no cycles

```
protocol
 |      \
model    ledger
 |         |
lean       |
   \      /
    check -> api -> cli, web -> agent
```

This is the graph `build.sbt` enforces between modules. Inside `model`, write
the package graph down as well: `term`, `types` and `vocabulary` at the bottom,
`node` and `kb` above them, and `example`, `runtime` and `testing` above those.

Bad: `model` (the DSL) importing from `example` and `runtime`, which in turn
import `node`: a package cycle inside the module. Good: `node <- example`,
`node <- runtime`, with no edge back.

Source: Volpe (layered modules); Bernhardt.

### M2 Concept packages

```
// bad
frflow/util/Helpers.scala, frflow/Types.scala
// good
frflow/refinement/Refines.scala, frflow/refinement/Parents.scala
```

Source: VirtusLab, "Code organization" (the `Types` suffix is the smell).

### M3 One type per file

```scala
// bad: two unrelated types in one file
final case class Keep(...)
final case class Exempt(...)
```

```scala
// good: one enum, its cases inside
enum Keeping:
  case Kept(invariant: NodeId, view: View)
  case Exempt(invariant: NodeId, because: String)
```

Source: the owner's rule (`docs/USAGE.md`: "One type to a file, in a package per
concept"); Scala style guide, "Files". VirtusLab bundles a sealed hierarchy, or
a service and the types only it builds, in one file. This repository uses an
enum instead.

### M4 Narrow visibility

```scala
// bad: root-wide visibility for a helper one package uses
private[frflow] def lambdaTypes(op: Param[?]): List[LeanType[?]]
```

```scala
// good
private[node] def lambdaTypes(op: Operation): List[LeanType[?]]
```

Source: Effective Scala, "Visibility" (easier to expand a public API than to
contract it); VirtusLab.

### M5 Package size

Bad: `protocol` with 24 files directly in it. Good: `protocol/id`,
`protocol/decision`, `protocol/snapshot`, `protocol/obligation`, each with 3 to
15 files.

Source: VirtusLab (split a package when it grows; avoid single-file packages).

### M6 `export` in the facade only

```scala
// bad: re-exports spread across packages, so a name has several import paths
// good: package frflow re-exports what a model writes, and nothing else does
export frflow.node.Node
export frflow.term.Term
```

Source: Scala 3 reference, "Export clauses".

## DSL design

### S1 Few, orthogonal entry points

Bad: several builders that build the same kind of node with different defaults.
Good: one builder per node kind (`claim`, `invariant`, `contract`,
`assumption`, `definition`, `design`), and modifiers that each set one thing.

Source: Li Haoyi, "Principle of Least Power" (published interfaces);
Odersky, "Lean Scala" (favour the core language over embedded DSLs: keep the DSL
small).

### S2 Builders return the precise case

```scala
// bad
inline def contract[F](op: Param[F])(...)(inline post: ...): Node[F]     // `leftOpenAbove` then needs require
```

```scala
// good
inline def contract[F](op: Param[F])(...)(inline post: ...): Contract[F]
extension [F](c: Contract[F]) def leftOpenAbove: Contract[F] = c.copy(fixes = Fixes.WordsLeftOpenAbove)
```

Source: Wlaschin; King.

### S3 Inline only for compile-time information

```scala
// bad: a large inline body, duplicated at every call site
inline def claim(id: String, statement: String, why: String)(inline formula: Term[Boolean]): Node[Unit] =
  /* 15 lines of construction */
```

```scala
// good: capture the source text and position, then call a plain method
inline def claim(id: String, statement: String, why: String)(inline formula: Term[Boolean]): Claim =
  Claims.make(id, statement, why, Lifted.thunk(() => formula, Source.text(formula)), Source.pos)
```

Source: Odersky, "Lean Scala" (macros only when simpler means are not enough);
Scala 3 reference, "Inline".

### S4 The DSL builds data

```scala
// bad: the knowledge base, which the DSL builds, also offers to run what it describes
final case class KnowledgeBase(...):
  def service[F](contract: Node[F])(bindings: Binding*): F = Wiring.service(this, contract, bindings)
  def exampleResults(n: Node[?]): List[ExampleResult] = ExampleRuns.results(this, n)
```

```scala
// good: the knowledge base is data; the interpreters take it as an argument
Wiring.service(kb, contract, bindings)    // in frflow.runtime
ExampleRuns.results(kb, contract)         // in frflow.example
```

Source: Ghosh (the algebra is separate from its interpreters); *FPiS* (a
description, and separate interpreters of the description).

## Views and DTOs

### V1 Derived by one function

```scala
// bad: a view assembled in each place that needs it, so the places drift apart
SnapNode(id, kind, content, hash, parents = ps, op = Some(o.name), rule = n.isInvariant, ...)   // in api, and again in cli
```

```scala
// good: one function in main code builds it (FrFlow does this in check/analysis/Snapshots.node)
object Snapshots:
  def node(n: Node, found: Checked, code: Option[CodeRef]): SnapNode = ...
```

Source: King ("strive for a single source of truth"; keep denormalized data
behind one module).

### V2 Keep the domain's shape

```scala
// bad: 31 fields, 27 of them optional or defaulted, one record for every kind
final case class SnapNode(id: NodeId, kind: NodeKind, content: Content, hash: Hash, parents: List[NodeId] = Nil,
    parts: List[NodeId] = Nil, replaces: Option[NodeId] = None, op: Option[String] = None, /* 23 more */)
```

```scala
// good: a common header, the kind's own data as a union, and what checks found kept apart
final case class SnapNode(id: NodeId, content: Content, hash: Hash, edges: SnapEdges, body: SnapBody) derives Codec.AsObject
enum SnapBody derives Codec.AsObject:
  case Claim(leaf: Leaf, split: Option[Split])
  case Contract(op: String, examples: List[ExampleView], code: Option[CodeRef])
  case Definition(defines: NonEmptyList[String])
  case Design(governs: NonEmptyList[RelPath])
```

Source: Wlaschin; King.

### V3 Group fields by concept

```scala
// bad: 30 counts in one record
final case class Overview(name: String, nodes: Int, proposed: Int, review: Int, accepted: Int, rejected: Int, gone: Int,
    proven: Int, /* ... */ runEveryCall: Int, runSampled: Int, runNotChecked: Int)
```

```scala
// good
final case class Overview(name: String, review: ReviewCounts, proofs: ProofCounts, tests: TestCounts,
    running: RunCheckCounts, complete: Boolean)
final case class ReviewCounts(proposed: Int, review: Int, accepted: Int, rejected: Int, gone: Int)
```

Source: D1 applied to views.

### V4 DTO defaults only for compatibility

```scala
// good, and only like this
/** `tested` is absent in snapshots written before tests were recorded. */
final case class SnapChecks(status: CheckStatus, tested: Option[TestReport] = None)
```

Source: Volpe (DTOs at the boundary).

### V5 Display text in the renderer

```scala
// bad
final case class SnapNode(...):
  def shownKind: String = kind.shown(rule)
```

```scala
// good
object NodeText:   // in cli/text
  def kind(b: SnapBody): String = b match { case _: SnapBody.Invariant => "invariant"; case _: SnapBody.Claim => "claim"; ... }
```

Source: B2 applied to views.

## Testing

### X1 Laws as property tests

```scala
// bad: one example per operation
test("parents"): assertEquals(kb.parents(a), Set(b))
```

```scala
// good
property("a node rests on every invariant it keeps"):
  forAll(genKb)(kb => kb.nodes.forall(n => kb.kept(n.id).subsetOf(kb.parents(n.id))))
```

Use the project's own generators (`frflow.testing`) or, with the owner's
approval, `munit-scalacheck`.

Source: *FPiS* chapter 8 (property-based testing) and chapters 7 to 9 (laws);
Ghosh (laws of the algebra).

### X2 Golden outputs

```scala
// good, as in cli/ViewsSuite: the views in plain mode against files in src/test/resources/golden
api.flatMap(_.tree(None)).map(t => golden("tree", TreeText.lines(t, st)))
```

Extend this to the generated Lean and the `--json` snapshot of each example
before a refactor of a core type.

### X3 Values in, values out

```scala
// bad: asserting that the API called the ledger
assert(fakeLedger.calls.contains("accept"))
```

```scala
// good: asserting what the operation returns and what state it leaves
assertEquals(api.accept(id).map(_.state), IO.pure(ReviewState.Accepted))
```

Source: Bernhardt (isolated tests of a functional core need no doubles);
Effective Scala (code to interfaces; fakes as implementations).

### X4 One scenario per test

```scala
// bad
test("decide"): /* accept, then reject, then accept again, with assertions after each */
```

```scala
// good
test("accepting a node waiting for review records the decision")
test("accepting a node whose hash changed is refused")
```

Source: VirtusLab (targeted tests).

## Comments

### C1 Scaladoc in domain words

```scala
// bad
/** Node class. */
```

```scala
// good
/** One statement in the developer's domain words, decided by them and proven in Lean from its parts. */
```

Source: Effective Scala, "Comments"; Scala style guide, "Scaladoc".

### C2 No history

```scala
// bad
// Was a Boolean before r41; now an enum so the CLI can show it.
```

```scala
// good
/** Whether the contract fixes a word the nodes above leave open. */
```

### C3 No defending the obvious

```scala
// bad
/** Returns the parents, not the children. Pure, not effectful. */
```

```scala
// good
/** The nodes this one rests on: its declared parents and the invariants it keeps. */
```

### C4 Restructure instead of explaining; name outside constraints

```scala
// bad: a comment narrating what a tangled block does step by step
// first we pick the check, then we sample, then we load the cells once, then ...
```

```scala
// good: a constraint the reader cannot see in the code
// Built in a method of its own: a file's top-level vals initialize in one JVM method (at most 64 KB).
```

Source: Effective Scala, "Comments" ("prefer 'obviously it works' to 'it works,
obviously'").

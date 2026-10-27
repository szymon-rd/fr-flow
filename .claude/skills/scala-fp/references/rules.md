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

### D4 Every domain value its own type, with its instances

```scala
// bad: paths as strings, and three Strings in a row that a caller can swap without a compile error
val governs: List[String] = Nil   // file paths
val file: String = ""             // the file the node is written in
Node(id: String, statement: String, why: String, ...)
```

```scala
// good
opaque type RelPath = String
object RelPath:
  def parse(s: String): Either[PathError, RelPath] =
    val p = java.nio.file.Path.of(s).normalize
    Either.cond(!p.isAbsolute && !p.startsWith(".."), p.toString, PathError.OutsideRoot(s))
  extension (p: RelPath) def under(root: java.nio.file.Path): java.nio.file.Path = root.resolve(p)
  given Eq[RelPath] = Eq.fromUniversalEquals
  given Order[RelPath] = Order.fromComparable[String]
  given Show[RelPath] = Show.fromToString

opaque type StatementText = String   // and `Why`, so the two cannot be swapped
final case class SourcePos(file: RelPath, line: Int)
```

`NodeId`, `Hash`, `KeyId` and `Fingerprint` in `protocol` are opaque types
already, and still need their `Eq`, `Show` and `Order` instances (T3).

Source: Volpe, *Practical FP in Scala* (a newtype for every domain value, with
derived instances); Scala 3 reference, "Opaque type aliases"; Li Haoyi,
"Practical Type Safety" (box ids, structured data instead of strings).

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
package frflow.runtime: object Enforce     { def wrap[Op](c: Node.Contract, impl: Op, plan: RunPlan): Op }
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
final case class RunPlan(checks: Map[NodeId, RunCheck], report: Violation => Unit)   // the wrapper runs inside the user's synchronous code
```

Source: Bernhardt (values at the boundary, the shell decides how to run);
Wlaschin, DMMF (workflows take their dependencies as parameters).

## Architecture: algebras, interpreters, programs, modules

### A1 Services and boundaries are algebras

```scala
// bad: a concrete class over IO, so every caller is tied to the file system and to IO
final class JsonStore[A: Decoder] private (file: Path, empty: A, print: A => String, lock: FileLock):
  def load: IO[A]
  def update[E, B](f: A => Either[E, (A, B)]): IO[Either[E, B]]
```

```scala
// good: what the ledger is to its users, in domain types, over any F
/** The developer's recorded decisions.
  * Laws: `record(d)` then `decisions` contains `d`; a refused record leaves `decisions` unchanged.
  */
trait Ledger[F[_]]:
  def decisions: F[List[Decision]]
  def record(d: Decision): F[Either[Refusal, Recorded]]
```

The same applies to `Git`, `Lake` (Lean's build tool) and `FrFlowApi`, which today
return `IO`.

Source: Volpe, *Practical FP in Scala* (algebras: `trait Brands[F[_]]`);
Ghosh (the algebra of a module); Effective Scala (short, orthogonal traits).

### A2 Interpreters built by smart constructors

```scala
// bad: construction is a side effect that happens outside F
val lock = new FileLock(file)   // opens the lock file
val ledger = new FileLedger(file, lock)
```

```scala
// good: the live interpreter is the companion's `make`, and holds its lock as a Resource
object Ledger:
  def make[F[_]: Async](file: Path): Resource[F, Ledger[F]] =
    FileLock.make[F](file).map(lock => FileLedger(file, lock))

// another interpreter, in its own file, for tests and dry runs; a Ref needs only Concurrent
final class InMemoryLedger[F[_]] private (ref: Ref[F, List[Decision]]) extends Ledger[F]:
  def decisions: F[List[Decision]] = ref.get
  def record(d: Decision): F[Either[Refusal, Recorded]] =
    ref.modify(ds => if ds.exists(_.node === d.node) then (ds, Left(Refusal.Twice(d.node))) else (d :: ds, Right(Recorded(d))))
object InMemoryLedger:
  def make[F[_]: Concurrent]: F[Ledger[F]] = Ref.of[F, List[Decision]](Nil).map(InMemoryLedger(_))
```

Source: Volpe (`Brands.make[F[_]: GenUUID: MonadCancelThrow](postgres: Resource[F, Session[F]])`);
cats-effect, "Resource" and "Ref".

### A3 Programs ask for the least capability

```scala
// bad: Sync lets the program do anything, so its type says nothing
def accept[F[_]: Sync](ledger: Ledger[F], keys: Keys[F])(id: NodeId, by: Developer): F[Either[Refusal, Decided]]
```

```scala
// good: the program composes algebras; it can sequence and read the clock, and nothing else
def accept[F[_]: Monad: Clock](ledger: Ledger[F], keys: Keys[F])(id: NodeId, by: Developer): F[Either[Refusal, Decided]] =
  (keys.of(by), Clock[F].realTimeInstant).tupled.flatMap((key, at) => ledger.record(Decision.accept(id, by, key, at)))
    .map(_.map(Decided(_)))
```

Source: Volpe (programs: `Checkout[F[_]: Background: Logger: MonadThrow: Retry]`);
cats-effect, "Type classes" overview (the capabilities in order of increasing
power, with capturing side effects the most powerful); De Goes ("Sync bloat"),
answered here by keeping `Sync` out of programs.

### A4 Algebras explicit, capabilities implicit

```scala
// bad: a service passed as a given, so a reader cannot see which ledger a program uses
def accept[F[_]: MonadThrow](id: NodeId)(using ledger: Ledger[F]): F[Decided]
```

```scala
// good: the algebra is a parameter; a capability is a context bound with a summoner
def accept[F[_]: MonadThrow: Clock](ledger: Ledger[F])(id: NodeId): F[Decided]

trait Processes[F[_]]:
  def run(cmd: Command): F[Run.Done]
object Processes:
  def apply[F[_]](using p: Processes[F]): Processes[F] = p
  given [F[_]: Async]: Processes[F] = ...   // one canonical instance
```

Source: Volpe, "Implicit vs explicit parameters" (`GenUUID[F]`, `Background[F]`
as capabilities with summoners; services passed explicitly).

### A5 Modules wire; IO is chosen once

```scala
// bad: IO fixed deep inside, and pieces built wherever they are needed
final class LiveApi private (kb: FrModel, ws: Workspace, cfg: Config, lake: Lake, git: Git, ledger: JsonStore[Ledger], ...)
```

```scala
// good: each layer has one `make`; the composition root fixes F = IO
final case class Services[F[_]](ledger: Ledger[F], git: Git[F], lake: Lake[F], disk: Disk[F])
object Services:
  def make[F[_]: Async](ws: Workspace): Resource[F, Services[F]] =
    (Ledger.make[F](ws.ledgerFile), Resource.pure(Git.make[F](ws.root)), Lake.make[F](ws.lean), Resource.pure(Disk.make[F]))
      .mapN(Services(_, _, _, _))

object Main extends IOApp.Simple:
  def run: IO[Unit] = Services.make[IO](Workspace.here).use(s => Cli.run(Programs.make(s)))
```

Source: Volpe (modules `Services`, `Programs`, `HttpApi`, and `Main` as the
composition root); cats-effect, `IOApp` and "Resource".

### A6 Initial or final encoding

```scala
// bad: terms as a tagless algebra, so FrFlow cannot print them to Lean, hash them or rewrite them
trait TermAlg[R[_]]:
  def lit(v: BigInt): R[BigInt]
  def add(a: R[BigInt], b: R[BigInt]): R[BigInt]
```

```scala
// good: what FrFlow inspects is an ADT; every interpreter is a total fold over it
enum Term[A]:
  case Lit(v: A)
  case Add(a: Term[BigInt], b: Term[BigInt]) extends Term[BigInt]
object LeanPrinter:  def print[A](t: Term[A]): Lean = ...
object Eval:         def eval[A](t: Term[A], env: Env): A = ...

// and what is only run stays final: a user's flow, run over models and over real boundaries
def expireOnce[F[_]: Monad](store: CrmStore[F], now: Instant): F[Unit]
```

Source: Chiusano and Bjarnason, *FPiS* (a description with separate
interpreters; algebraic design); Ghosh (algebra and interpreters).

## Type classes, instances and laws

### T1 Structure with cats

```scala
// bad: a hand-written fold with an accumulator and a mutable builder
val out = Vector.newBuilder[ExampleResult]
for e <- n.cases do out += run(e)
out.result().toList
```

```scala
// good
n.cases.traverse(run)               // F[List[ExampleResult]] when run returns F
kb.nodes.foldMap(n => Counts.of(n))  // with a Monoid[Counts]
(load, keys, checks).parMapN(Inputs(_, _, _))
```

Source: cats documentation, "Traverse", "Foldable", "Parallel".

### T2 Semigroup and Monoid for combining

```scala
// bad: Overview computed by thirty separate counts over the same list
contracts = contracts.size, contractsProvenDown = contracts.count(provenDown), examplesInLean = inLean.size, ...
```

```scala
// good: one count per node, combined by the Monoid
final case class ProofCounts(proven: Int, splits: Int, splitsProven: Int)
object ProofCounts:
  given Monoid[ProofCounts] = Monoid.instance(ProofCounts(0, 0, 0),
    (a, b) => ProofCounts(a.proven + b.proven, a.splits + b.splits, a.splitsProven + b.splitsProven))
  def of(n: SnapNode): ProofCounts = ...
val proofs = nodes.foldMap(ProofCounts.of)
```

Source: cats documentation, "Semigroup" and "Monoid".

### T3 Instances in companions

```scala
// bad: equality by `==` on an opaque String, sorting with an ad hoc Ordering at call sites
nodes.sortBy(_.id.value)
if a.id == b.id then ...
```

```scala
// good
opaque type NodeId = String
object NodeId:
  def parse(s: String): Either[IdError, NodeId] = ...
  given Eq[NodeId] = Eq.fromUniversalEquals
  given Order[NodeId] = Order.by(_.value)
  given Show[NodeId] = Show.show(_.value)
  given Ordering[NodeId] = Order[NodeId].toOrdering   // for the standard library's sortBy and sorted
  extension (id: NodeId) def value: String = id

nodes.sortBy(_.id)
if a.id === b.id then ...
```

Source: cats documentation, "Eq", "Order", "Show"; Volpe (instances derived
for every newtype).

### T4 Canonical, lawful instances

```scala
// bad: a Monoid whose combine keeps the left side, so it is not associative with its empty for every value
given Monoid[Content] = Monoid.instance(Content.empty, (a, _) => a)
```

```scala
// good: the instance obeys the laws and a law test says so (X1); an unlawful operation is a named function
given Monoid[Diagnostics] = Monoid.instance(Diagnostics.empty, _ ++ _)
def preferFirst(a: Content, b: Content): Content = a
```

Source: cats, "Law testing"; Scala 3 reference, "Given instances" (canonical
values).

### T5 Coherence

```scala
// bad: an instance in an unrelated object, imported in some files and not others
object JsonStuff:
  given Codec[NodeId] = ...
```

```scala
// good
object NodeId:
  given Codec[NodeId] = Codec.from(Decoder.decodeString, Encoder.encodeString)
```

Source: Scala 3 reference (implicit scope); cats guidelines (instance placement
and priority).

### T6 Implicit conversions only for DSL literal lifting

```scala
// bad: a conversion that hides an access
given ops[T]: Conversion[Boundary[T], T] = _.ops
```

```scala
// good: lifting literals into terms, all in one file, and an explicit accessor elsewhere
given int: Conversion[Int, Term[BigInt]] = i => Term.lit(BigInt(i))
db.ops.fetch(user)
```

Source: Scala 3 reference, "Contextual abstractions" (most implicit conversions
are of dubious value).

### T7 `using` for type classes, capabilities and witnesses

```scala
// bad: configuration and a service smuggled in as givens
def check(node: NodeId)(using cfg: Config, lake: Lake[IO]): IO[Verdict]
```

```scala
// good
def check[F[_]: MonadThrow](lake: Lake[F], cfg: Config)(node: NodeId): F[Verdict]
def contract[F](op: Param[F])(using s: Sig[F]): ...   // a typing witness is context
```

Source: Scala 3 reference, "Using clauses"; Volpe (A4).

### T8 Extension methods for opaque APIs and syntax

```scala
// bad: interpreters attached to Node through extensions in Node.scala
extension (n: Node[?]) private[frflow] def postFn: Option[(List[Any], Any) => Boolean]
```

```scala
// good
object Hash:
  extension (h: Hash) def short: String = h.take(8)
```

Source: Scala 3 reference, "Opaque type aliases".

### T9 Codecs on DTOs only

```scala
// bad
enum Node derives Codec.AsObject
```

```scala
// good
final case class SnapNode(...) derives Codec.AsObject   // in protocol
```

Source: Volpe (domain types separate from request and response types).

### T10 Transformers inside programs and out of algebras

```scala
// bad: a transformer in the algebra's signature leaks into every interpreter and caller
trait Ledger[F[_]]:
  def record(d: Decision): EitherT[F, Refusal, Recorded]
```

```scala
// good: the algebra returns F[Either[...]]; a program chaining several such steps uses EitherT locally
def acceptAll[F[_]: Monad](ledger: Ledger[F])(ds: List[Decision]): F[Either[Refusal, List[Recorded]]] =
  ds.traverse(d => EitherT(ledger.record(d))).value
```

Source: cats documentation, "EitherT".

## Effects

### E1 Pure core

```scala
// bad: the FrModel, a core aggregate, imports cats.effect and the runtime wiring
package frflow.kb
import cats.effect.IO
import frflow.runtime.Wiring
```

```scala
// good: the core is values and functions; the runtime module takes a FrModel
package frflow.runtime
def wire[F[_]: Async](kb: FrModel, impls: Implementations[F]): Resource[F, Running[F]]
```

Source: *FPiS* chapter 13 ("inside every function with side effects is a pure
function waiting to get out"); Bernhardt.

### E2 Read inputs once, then call the core

```scala
// good, the shape of check.Inputs.read, over F: all reads in parallel and once, then pure code
def verdict[F[_]: MonadThrow: Parallel: Clock](disk: Disk[F], ledger: Ledger[F])(kb: FrModel): F[Verdict] =
  (disk.read(kb.idea), ledger.decisions, Clock[F].realTimeInstant).parMapN(Inputs(_, _, _)).map(Verdict.of(kb, _))
```

```scala
// bad: the pure function reaches for the file system itself
def verdict(kb: FrModel): Verdict = Verdict(kb, Files.readString(Path.of(kb.idea)))
```

Source: Bernhardt; Volpe (programs compose algebras).

### E3 Side effects suspended in interpreters

```scala
// bad: the write happens when the method is called, outside F
def save(f: Path, s: String): IO[Unit] = { Files.writeString(f, s); IO.unit }
```

```scala
// good: in the interpreter, blocking file I/O on the blocking pool
def save(f: Path, s: String): F[Unit] = Sync[F].blocking(Files.writeString(f, s)).void
```

Source: cats-effect, "Concepts" and "Thread model".

### E4 Every lifecycle is a Resource

```scala
// good, as in check/process/Run: fs2's spawn is a Resource, so the process ends with `use`
ProcessBuilder(command, args).withWorkingDirectory(dir).spawn[F].use(p => collect(p))
// a background fiber that ends with the server
Supervisor[F].flatMap(sup => Resource.eval(sup.supervise(watchSources)))
```

```scala
// bad: a process that is never destroyed when the fiber is cancelled
Sync[F].blocking(java.lang.ProcessBuilder(cmd*).start()).flatMap(read)
```

Source: cats-effect, "Resource" and "Supervisor"; fs2 `Processes`.

### E5 cats-effect and fs2 for state, coordination and streams

```scala
// bad: a class holding state in an AtomicReference, and a callback for progress
final class FaultPlan(faults: List[Boolean]):
  private val left = AtomicReference(faults)
def check(node: Option[NodeId], progress: Progress => IO[Unit] = _ => IO.unit): IO[CheckReport]
```

```scala
// good: state in a Ref, a one-time signal in a Deferred, progress as a Stream
final class Faults[F[_]] private (left: Ref[F, List[Fault]]):
  def next: F[Option[Fault]] = left.modify(fs => (fs.drop(1), fs.headOption))
def ready: F[Deferred[F, Unit]]
def check(node: Option[NodeId]): Stream[F, CheckEvent]   // enum CheckEvent { case Level(p: Progress); case Done(r: CheckReport) }
```

Allowed with a comment: the function `service` returns is called synchronously
by the user's program, outside `F`, so its per-wrapper cache is an
`AtomicReference` local to that wrapper.

Source: cats-effect, "Ref", "Deferred", "Queue"; fs2 guide.

### E6 Effects run in IOApp; callbacks through a Dispatcher

```scala
// bad: deep inside the example runner
Flows.run[IO](steps, env, impls, bindings, Some(pause)).attempt.unsafeRunSync()
```

```scala
// good: an impure callback enters F through a Dispatcher held for the server's lifetime
Dispatcher.parallel[F].map(d => (msg: String) => d.unsafeRunAndForget(queue.offer(msg)))
// and the one synchronous bridge, named and documented
object RunWhileLoading:
  /** The examples run while the model loads, before any IOApp exists. */
  def apply[A](io: IO[A])(using IORuntime): Either[Throwable, A] = io.attempt.unsafeRunSync()
```

Source: cats-effect, "Dispatcher" and `IOApp`.

### E7 Time, randomness and ids as capabilities

```scala
// bad
def sign(d: Decision): Signed = Signed(d, Instant.now())
```

```scala
// good
def sign[F[_]: Functor: Clock](d: Decision): F[Signed] = Clock[F].realTimeInstant.map(Signed(d, _))
```

Source: cats-effect, "Clock", "Random" and `UUIDGen`.

### E8 Warnings for discarded effects

```scala
// bad: compiles, and the log line never runs
def accept[F[_]: Monad: Log](...): F[Decided] =
  Log[F].info(s"accepted $id")
  ledger.record(d)
```

With `-Wnonunit-statement` this is an error. The fix is `Log[F].info(...) *> ledger.record(d)`.

Source: cats-effect FAQ ("What do non-unit statement warnings mean?"); VirtusLab.

## Errors

### R1 Error ADTs per module

```scala
// bad
def accept(id: NodeId): IO[Either[String, Decision]]
```

```scala
// good
enum Refusal extends NoStackTrace:
  case NotWaiting(id: NodeId, state: ReviewState)
  case Unsigned(id: NodeId)
  case StaleHash(id: NodeId, decided: Hash, now: Hash)
```

Source: Volpe (error ADTs extending `NoStackTrace`); cats, "ApplicativeError and
MonadError".

### R2 Choose the channel by who handles the error

```scala
// bad: a refusal the CLI must explain is thrown, and an I/O failure nobody can fix is returned as a value
def record(d: Decision): F[Recorded]                          // raises Refusal
def load: F[Either[IOException, Ledger]]
```

```scala
// good
def record(d: Decision): F[Either[Refusal, Recorded]]   // the caller branches on the refusal
def load: F[Ledger]                                     // a broken file is raised as LedgerError.BadFile
api.status.recoverWith { case e: LedgerError => Console[F].errorln(Show[LedgerError].show(e)).as(ExitCode(3)) }
```

Source: cats documentation, "ApplicativeError and MonadError"; Volpe.

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
(uniqueIds(kb), parentsDeclared(kb), pathsExist(kb)).parMapN((_, _, _) => kb)   // EitherNec[ModelError, _]
```

Source: cats, "Validated" and "Parallel".

### R4 Map errors in interpreters, render at the edge

```scala
// bad: a circe error escapes the ledger, and the ledger builds CLI text
IO.fromEither(decode[A](text))
Left(s"${Colors.red("refused")}: $id is not waiting")
```

```scala
// good
Sync[F].fromEither(decode[A](text)).adaptError(e => LedgerError.BadFile(file, e.getMessage))
// cli renders with Show[Refusal]
```

Source: Volpe (`adaptError` in programs and interpreters).

## Functions

### F1 One job per function

`enforce` chooses the check, builds the sampler, caches what each assumption
was last checked against, binds parameters, runs the code, checks the result,
reports and throws: about eight jobs in 30 lines.

```scala
// good: an orchestration of named steps, each testable alone
def wrap[Op](c: Node.Contract, impl: Op, plan: RunPlan): Op =
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
def wrap[Op](c: Node.Contract, impl: Op, plan: RunPlan): Op
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
def wrap[Op](c: Node.Contract, impl: Op, plan: RunPlan): Op
def service[Op](c: Contract[Op], impl: Op, check: RunCheck = RunCheck.EveryCall): Service[Op]   // DSL entry point
```

Source: Effective Scala, "Dependency injection"; VirtusLab (lawful APIs); Li
Haoyi ranks default arguments as a low-power form of dependency injection,
which is why they stay allowed on published entry points.

### F7 `require` only for FrFlow bugs

```scala
// bad: a mistake in the developer's model reported by an exception from a builder
require(kind == NodeKind.Contract, s"$id: only a contract fixes a word left open above")
```

```scala
// good: the method exists only on Contract (S2); what types cannot express is collected
def validate(kb: FrModel): ValidatedNec[ModelError, FrModel]
// and a FrFlow bug may still be asserted
assert(index.size == all.size, "Bindings.index dropped a parameter")
```

Source: Effective Scala, "`require` and `assert`" (executable documentation
where types cannot express the invariant); VirtusLab (`Either` instead of
`require` for recoverable failures); King.

### F8 No exceptions for control flow

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

### F9 `var` only inside a method

```scala
// bad: a printer object with ten mutable fields and a mutable depth counter, so printing has hidden order
private val defs = mutable.ListBuffer.empty[Def[?]]
private val boundaries = mutable.LinkedHashSet.empty[Boundary[?]]
private var negations = 0
private def negated[T](f: => T): T = { negations += 1; try f finally negations -= 1 }
```

```scala
// good: what printing collects is a value with a Monoid, and the depth is a parameter
final case class Uses(defs: List[Def[?]], boundaries: Set[Boundary[?]], errors: Set[ErrorType])
object Uses:
  given Monoid[Uses] = Monoid.instance(Uses(Nil, Set.empty, Set.empty), (a, b) =>
    Uses(a.defs ++ b.defs, a.boundaries ++ b.boundaries, a.errors ++ b.errors))
def expr(t: Tree, negations: Int): (Lean, Uses)
```

Source: VirtusLab (no class-level `var`; immutable collections); cats
documentation, "Monoid".

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

// good: an algebra and its companion, whose `make` is the live interpreter (Ledger.scala)
trait Ledger[F[_]]: ...
object Ledger:
  def make[F[_]: Async](file: Path): Resource[F, Ledger[F]] = ...
// the in-memory interpreter in InMemoryLedger.scala, a class and its companion
```

Source: the owner's rule (`docs/USAGE.md`: "One type to a file, in a package per
concept"); Volpe (`trait Brands[F[_]]` and `object Brands { def make ... }` in
one file); Scala style guide, "Files". VirtusLab bundles a sealed hierarchy, or
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
// bad: the FrModel, which the DSL builds, also offers to run what it describes
final case class FrModel(...):
  def service[F](contract: Node[F])(bindings: Binding*): F = Wiring.service(this, contract, bindings)
  def exampleResults(n: Node[?]): List[ExampleResult] = ExampleRuns.results(this, n)
```

```scala
// good: the FrModel is data; the interpreters take it as an argument
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

### X1 Law-test every instance with discipline

```scala
// bad: an instance given and never checked against its laws
given Monoid[ProofCounts] = ...
```

```scala
// good
import cats.kernel.laws.discipline.{MonoidTests, OrderTests}
import munit.DisciplineSuite

class CountsLaws extends DisciplineSuite:
  import Generators.given          // Arbitrary and Cogen instances, one generators file per module
  checkAll("Monoid[ProofCounts]", MonoidTests[ProofCounts].monoid)
  checkAll("Order[NodeId]", OrderTests[NodeId].order)
```

A `Functor` or `Traverse` instance on a FrFlow container (a tree of nodes, a
term with holes) is checked with `FunctorTests[T].functor[Int, Int, String]`
or `TraverseTests[T].traverse[...]`, and needs `Eq[T[A]]` and `Arbitrary[T[A]]`.

Test dependencies to add, at versions matching cats and munit: `cats-laws`,
`cats-kernel-laws`, `discipline-munit`, `munit-scalacheck`, `scalacheck`, and
`scalacheck-effect-munit` for properties in `F` (`forAllF`, X2).

Source: cats documentation, "Law testing"; discipline; discipline-munit; Volpe
(`checkAll("Monoid[Money]", MonoidTests[Money].monoid)` in the companion
repository).

### X2 Laws for algebras, run against every interpreter

```scala
// bad: the in-memory ledger is tested, the file ledger is not, and nothing says they agree
test("record then list"): ...
```

```scala
// good: one property suite states the algebra's laws; each interpreter runs it
abstract class LedgerLaws(make: Resource[IO, Ledger[IO]]) extends CatsEffectSuite with ScalaCheckEffectSuite:
  test("a recorded decision is listed"):
    forAllF((d: Decision) => make.use(l => l.record(d) *> l.decisions).map(ds => assert(ds.exists(_ === d))))
  test("a refused record changes nothing"):
    forAllF((d: Decision) => make.use(l => l.record(d) *> l.decisions.flatMap(before =>
      l.record(d) *> l.decisions.map(after => assertEquals(after, before)))))

class InMemoryLedgerSuite extends LedgerLaws(Resource.eval(InMemoryLedger.make[IO]))
class FileLedgerSuite     extends LedgerLaws(Files[IO].tempDirectory.flatMap(d => Ledger.make[IO](d.toNioPath.resolve("ledger.json"))))
```

The DSL's algebras get property tests too: `parents` contains every invariant
a node keeps; evaluating a term in Scala agrees with Lean's evaluation on
generated examples; printing then parsing a snapshot is the identity.

Source: *FPiS* chapter 8 (property-based testing) and chapters 7 to 9 (laws);
Ghosh (laws of the algebra); Volpe (interpreters tested against the same
expectations).

### X3 Golden outputs

```scala
// good, as in cli/ViewsSuite: the views in plain mode against files in src/test/resources/golden
api.flatMap(_.tree(None)).map(t => golden("tree", TreeText.lines(t, st)))
```

Extend this to the generated Lean and the `--json` snapshot of each example
before a refactor of a core type.

### X4 Values in, values out; fakes are interpreters

```scala
// bad: asserting that the API called the ledger
assert(fakeLedger.calls.contains("accept"))
```

```scala
// good: an in-memory interpreter, and assertions on what the program returns and leaves
for
  ledger <- InMemoryLedger.make[IO]
  out    <- Programs.accept(ledger, keys)(id, alice)
  ds     <- ledger.decisions
yield assertEquals((out.isRight, ds.map(_.node)), (true, List(id)))
```

Time-dependent code (timeouts, retries, sampling) is tested with
`cats.effect.testkit.TestControl`, never with real sleeps.

Source: Bernhardt (no doubles for a functional core); Volpe (test
interpreters); cats-effect testkit.

### X5 One scenario per test

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

package frflow.dsl

import frflow.lift.{Code, Schema}
import scala.collection.mutable.ListBuffer

/** The role of a layer in the refinement chain. */
enum LayerKind:
  /** The root: the most abstract behaviour and the requirements it must satisfy. */
  case Requirements
  /** A design step: refines its parent toward an implementation. */
  case Design
  /** The last refinement: executable Scala, run by `frflow.runtime`. */
  case Implementation

  def label: String = this match
    case Requirements   => "requirements"
    case Design         => "design"
    case Implementation => "implementation"

/** A named state predicate. Requirements are invariants of the root layer that
  * state what the system must guarantee; every refining layer inherits them.
  */
final class InvariantDecl[S] private[dsl] (val name: String, val doc: String, val requirement: Boolean, val code: Code[S => Boolean])

/** What an operation refines in the parent layer. */
enum OpTarget:
  case Unspecified
  /** A new operation that leaves the parent state unchanged. */
  case Skip
  /** Refines `parent`; `witness` gives the parent operation's parameters. */
  case Refines(parent: Operation[?, ?], witness: Code[Any])

/** An operation of a layer: a guarded state transition with parameters of type `P`.
  *
  * The guard is the conjunction of `assume` clauses (environment assumptions,
  * not checked at run time) and `check` clauses (conditions the system enforces).
  * The effect `act` gives the new state; without it the state is unchanged.
  */
final class Operation[S, P] private[dsl] (val layer: Layer[S], val name: String, val doc: String, val paramSchema: Schema[P]):
  private var assumeBuf = Vector.empty[(Assumption, Code[(S, P) => Boolean])]
  private var checkBuf = Vector.empty[Code[(S, P) => Boolean]]
  private var effect: Option[Code[(S, P) => S]] = None
  private var tgt: OpTarget = OpTarget.Unspecified

  def assumes: Vector[(Assumption, Code[(S, P) => Boolean])] = assumeBuf
  def checks: Vector[Code[(S, P) => Boolean]] = checkBuf
  def action: Option[Code[(S, P) => S]] = effect
  def target: OpTarget = tgt

  /** A condition the system enforces. Several clauses are conjoined. */
  inline def check(inline f: (S, P) => Boolean): Operation[S, P] = addCheck(Code(f))

  /** An environment assumption, justified by `a`. Not checked at run time. */
  inline def assume(a: Assumption)(inline f: (S, P) => Boolean): Operation[S, P] = addAssume(a, Code(f))

  /** The new state. */
  inline def act(inline f: (S, P) => S): Operation[S, P] = setAct(Code(f))

  /** Refines operation `parent` of the parent layer; `witness` builds its parameters. */
  inline def refines[Q](parent: Operation[?, Q])(inline witness: (S, P) => Q): Operation[S, P] =
    setRefines(parent, Code(witness))

  /** A new operation that does not change the state of the parent layer. */
  def refinesSkip: Operation[S, P] =
    tgt = OpTarget.Skip
    this

  def addCheck(c: Code[(S, P) => Boolean]): Operation[S, P] =
    checkBuf :+= c
    this

  def addAssume(a: Assumption, c: Code[(S, P) => Boolean]): Operation[S, P] =
    assumeBuf :+= (a -> c)
    this

  def setAct(c: Code[(S, P) => S]): Operation[S, P] =
    effect = Some(c)
    this

  def setRefines(parent: Operation[?, ?], witness: Code[Any]): Operation[S, P] =
    tgt = OpTarget.Refines(parent, witness)
    this

  /** Whether the guard's `check` clauses hold. */
  def enabled(s: S, p: P): Boolean = checkBuf.forall(_.value(s, p))

  /** The effect, without checking the guard. */
  def apply(s: S, p: P): S = effect.fold(s)(_.value(s, p))

  override def toString: String = s"${layer.id}.$name"

/** A layer of the model. Its state is a Scala ADT `S`. */
sealed abstract class Layer[S](
    val id: String,
    val name: String,
    val statement: String,
    val rationale: String
)(using val stateSchema: Schema[S]):
  private val opBuf = ListBuffer.empty[Operation[S, ?]]
  private val invBuf = ListBuffer.empty[InvariantDecl[S]]
  private val citeBuf = ListBuffer.empty[Assumption]

  def kind: LayerKind
  def theory: Theory
  def parentLayer: Option[Layer[?]]

  final def operations: List[Operation[S, ?]] = opBuf.toList
  final def invariants: List[InvariantDecl[S]] = invBuf.toList
  final def cited: List[Assumption] = citeBuf.toList

  /** Declares an operation with parameters of type `P` (usually a case class). */
  protected final def operation[P](name: String, doc: String = "")(using p: Schema[P]): Operation[S, P] =
    val op = Operation[S, P](this, name, doc, p)
    opBuf += op
    op

  /** An invariant of this layer, proven inductive. */
  protected inline def invariant(name: String, doc: String = "")(inline p: S => Boolean): Unit =
    registerInvariant(name, doc, requirement = false, Code(p))

  /** Assumptions about the environment the design of this layer relies on. */
  protected final def assumes(as: Assumption*): Unit = citeBuf ++= as

  protected final def registerInvariant(name: String, doc: String, requirement: Boolean, code: Code[S => Boolean]): Unit =
    invBuf += InvariantDecl(name, doc, requirement, code)

  override def toString: String = s"$id $name"

/** A layer with a predicate on initial states. */
sealed abstract class AbstractLayer[S](id: String, name: String, statement: String, rationale: String)(using Schema[S])
    extends Layer[S](id, name, statement, rationale):
  private var initCode: Option[Code[S => Boolean]] = None
  def initial: Option[Code[S => Boolean]] = initCode

  /** The initial states. */
  protected inline def init(inline p: S => Boolean): Unit = setInit(Code(p))

  protected final def setInit(c: Code[S => Boolean]): Unit = initCode = Some(c)

/** The root layer: the most abstract behaviour, and the requirements it satisfies.
  *
  * {{{
  * object R0 extends Requirements[AuditState](AuthzTheory, "R0", "NoUnauthorizedAccess",
  *     statement = "...", rationale = "..."):
  *   init(s => s.version == 0 && s.log.isEmpty)
  *   val access = operation[AccessAs]("access").check(...).act(...)
  *   requirement("Safe", "...")(s => ...)
  * }}}
  */
abstract class Requirements[S](val theory: Theory, id: String, name: String, statement: String, rationale: String)(
    using Schema[S]
) extends AbstractLayer[S](id, name, statement, rationale):
  final def kind: LayerKind = LayerKind.Requirements
  final def parentLayer: Option[Layer[?]] = None

  /** A requirement: a property every refinement, including the implementation, must preserve. */
  protected inline def requirement(name: String, statement: String)(inline p: S => Boolean): Unit =
    registerInvariant(name, statement, requirement = true, Code(p))

/** Parts shared by refining layers: the link to the parent. */
sealed trait Refining[S, A]:
  self: Layer[S] =>
  def parent: Layer[A]
  private var absCode: Option[Code[S => A]] = None
  private var glueCode: Option[Code[S => Boolean]] = None

  def abstractionCode: Option[Code[S => A]] = absCode
  def glueInvariant: Option[Code[S => Boolean]] = glueCode

  /** Maps a state of this layer to the state of the parent layer it represents. */
  protected inline def abstraction(inline f: S => A): Unit = setAbstraction(Code(f))

  /** Gluing invariant: relates this layer's state to the parent's; proven inductive. */
  protected inline def glue(inline p: S => Boolean): Unit = setGlue(Code(p))

  protected final def setAbstraction(c: Code[S => A]): Unit = absCode = Some(c)
  protected final def setGlue(c: Code[S => Boolean]): Unit = glueCode = Some(c)

/** A design layer: refines its parent toward an implementation. */
abstract class Refinement[S, A](val parent: Layer[A], id: String, name: String, statement: String, rationale: String)(
    using Schema[S]
) extends AbstractLayer[S](id, name, statement, rationale), Refining[S, A]:
  final def kind: LayerKind = LayerKind.Design
  final def theory: Theory = parent.theory
  final def parentLayer: Option[Layer[?]] = Some(parent)

/** The implementation: the last refinement. Its state is concrete data, its
  * initial state is a value, and its operations are executable Scala.
  * `frflow.runtime.Service` runs it.
  */
abstract class Implementation[S, A](val parent: Layer[A], id: String, name: String, statement: String, rationale: String)(
    using Schema[S]
) extends Layer[S](id, name, statement, rationale), Refining[S, A]:
  final def kind: LayerKind = LayerKind.Implementation
  final def theory: Theory = parent.theory
  final def parentLayer: Option[Layer[?]] = Some(parent)

  private var initialCode: Option[Code[S]] = None
  def initialState: Option[Code[S]] = initialCode

  /** The initial state. */
  protected inline def initial(inline s: S): Unit = setInitial(Code(s))

  protected final def setInitial(c: Code[S]): Unit = initialCode = Some(c)

/** A model: a theory and its layers, from the requirements down to the implementation. */
class Model(val theory: Theory, layerList: Layer[?]*):
  def layers: List[Layer[?]] = layerList.toList
  def layer(id: String): Option[Layer[?]] = layers.find(_.id == id)

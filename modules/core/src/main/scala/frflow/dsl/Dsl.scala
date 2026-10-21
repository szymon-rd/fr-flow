package frflow.dsl

import frflow.model.*
import scala.collection.mutable.ListBuffer

/** Base class for a theory written in the FrFlow DSL.
  *
  * {{{
  * object Authz extends TheoryDef("Authz"):
  *   vocabulary(opaqueType("User", "A principal."))
  *   val T0 = root("T0", "NoUnauthorizedAccess", statement = "...", rationale = "...")(
  *     NodeSpec(...)
  *   )
  *   val T1 = T0.refine("T1", "AuthnThenAuthz", statement = "...", rationale = "...")(
  *     link = Link(...), spec = NodeSpec(...)
  *   )
  * }}}
  *
  * Node and assumption declarations register themselves in declaration order.
  * `model` returns the immutable theory; validation is done separately by `frflow.lint`.
  */
abstract class TheoryDef(val name: String):
  private val vocabBuf = ListBuffer.empty[VocabEntry]
  private val assumptionBuf = ListBuffer.empty[Assumption]
  private val nodeBuf = ListBuffer.empty[Node]

  final def model: TheoryModel =
    TheoryModel(name, vocabBuf.toList, assumptionBuf.toList, nodeBuf.toList)

  protected final def vocabulary(entries: VocabEntry*): Unit = vocabBuf ++= entries

  protected final def assumption(id: String, name: String, statement: String, justification: String): AssumptionRef =
    assumptionBuf += Assumption(id, name, statement, justification)
    AssumptionRef(id)

  protected final def root(id: String, name: String, statement: String, rationale: String)(spec: NodeSpec): NodeRef =
    nodeBuf += Node(id, name, statement, rationale, parent = None, link = None, spec)
    NodeRef(id)

  extension (parent: NodeRef)
    protected final def refine(id: String, name: String, statement: String, rationale: String)(
        link: Link,
        spec: NodeSpec
    ): NodeRef =
      nodeBuf += Node(id, name, statement, rationale, parent = Some(parent.id), link = Some(link), spec)
      NodeRef(id)

/** Handle to a declared node. */
final case class NodeRef(id: String)

/** Handle to a declared assumption, used in `assume` clauses. */
final case class AssumptionRef(id: String)

// ---------------------------------------------------------------------------
// Construction helpers. Lean fragments are passed as plain strings.
// ---------------------------------------------------------------------------

def opaqueType(name: String, doc: String): VocabEntry = VocabEntry.Opaque(name, doc)

def typeAlias(name: String, lean: String, doc: String): VocabEntry = VocabEntry.Alias(name, LeanExpr(lean), doc)

def lean(text: String): LeanExpr = LeanExpr(text.stripMargin.trim)

def field(name: String, tpe: String, doc: String = ""): Field = Field(name, LeanExpr(tpe), doc)

/** `state("version" -> "Nat", "log" -> "List Entry")` */
def state(fields: (String, String)*): Seq[Field] = fields.map((n, t) => Field(n, LeanExpr(t)))

def invariant(name: String, expr: String, doc: String = ""): InvariantDef = InvariantDef(name, LeanExpr(expr), doc)

def link(abs: String, glue: String = ""): Link =
  Link(LeanExpr(abs), Option(glue).map(_.trim).filter(_.nonEmpty).map(LeanExpr(_)))

def event(name: String): EventDef = EventDef(name)

extension (e: EventDef)
  def doc(text: String): EventDef = e.copy(description = text)
  def params(ps: (String, String)*): EventDef =
    e.copy(parameters = e.parameters ++ ps.map((n, t) => Field(n, LeanExpr(t))))

  /** Environment assumption clause, justified by the given assumption. */
  def assume(a: AssumptionRef, expr: String): EventDef =
    e.copy(assumes = e.assumes :+ AssumeClause(a.id, LeanExpr(expr)))

  /** Condition the implementation must enforce. Several clauses are conjoined. */
  def check(expr: String): EventDef = e.copy(checks = e.checks :+ LeanExpr(expr))

  /** New state, as a Lean expression over `s` and `p`. Omitted: state unchanged. */
  def act(expr: String): EventDef = e.copy(action = Some(LeanExpr(expr)))

  def refines(parentEvent: String, witness: String): EventDef =
    e.copy(target = EventTarget.Refines(parentEvent, LeanExpr(witness)))

  def refinesSkip: EventDef = e.copy(target = EventTarget.Skip)

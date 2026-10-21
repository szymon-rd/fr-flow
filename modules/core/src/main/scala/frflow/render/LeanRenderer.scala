package frflow.render

import frflow.ir.*
import frflow.model.*
import frflow.obligation.{Obligation, Obligations}
import frflow.render.LeanPrinter as P

/** A property guaranteed at a layer: declared there, or inherited from an
  * ancestor through the chain of abstraction functions.
  *
  * @param origin    layer that declares the invariant
  * @param chain     layer ids from the guaranteeing layer up to (excluding) `origin`
  */
final case class Guarantee(origin: String, invariant: String, requirement: Boolean, chain: List[String]):
  def isOwn: Boolean = chain.isEmpty

  /** Name of the theorem proving this guarantee, relative to the theory namespace. */
  def theoremName: String = chain.headOption match
    case None        => s"$origin.${invariant}_holds"
    case Some(layer) => s"$layer.inherits_${origin}_$invariant"

  /** Lean predicate over the guaranteeing layer's state. */
  def predicate: String =
    if isOwn then invariant
    else s"fun s => $origin.$invariant (${chain.foldLeft("s")((acc, id) => s"$id.abs ($acc)")})"

object Nodes:
  /** Id of the theory node (domain and laws) in the ledger, the checker and reports. */
  val TheoryId = "Theory"

/** Renders a model to Lean.
  *
  * Layout, relative to the Lean workspace (`<T>` is the theory name, `<N>` a node:
  * `Theory` or a layer id):
  *   - `FrFlowGen/<T>/Domain.lean`            ADTs and functions translated from Scala
  *   - `FrFlowGen/<T>/<L>/Model.lean`         a layer: state, operations, invariants, link
  *   - `FrFlowGen/<T>/<N>/Obligations.lean`   obligation statements
  *   - `FrFlowGen/<T>/<N>/Auto.lean`          `frflow_auto` attempts for obligations without authored proofs
  *   - `FrFlowGen/<T>/<N>/Assembly.lean`      kernel theorems built from the proofs
  *   - `FrFlowAudit/<T>/<N>.lean`             axiom audit script
  *
  * Authored proofs are never generated: they live in `Proofs/<T>/<N>.lean`.
  *
  * @param authored obligation names that have an authored proof, per node
  */
final class LeanRenderer(m: TheoryModel, authored: Map[String, Set[String]] = Map.empty):
  import LeanRenderer.*

  private val T = m.name
  val TheoryId: String = Nodes.TheoryId

  /** Node ids in verification order: the theory, then layers parents first. */
  def nodeIds: List[String] = TheoryId :: m.topological.map(_.id)

  def isAuthored(node: String, obligation: String): Boolean = authored.getOrElse(node, Set.empty)(obligation)
  def hasProofFile(node: String): Boolean = authored.get(node).exists(_.nonEmpty)

  // -- module names and paths ------------------------------------------------

  def domainModule: String = s"FrFlowGen.$T.Domain"
  def domainPath: String = s"FrFlowGen/$T/Domain.lean"
  def modelModule(id: String): String = s"FrFlowGen.$T.$id.Model"
  def modelPath(id: String): String = s"FrFlowGen/$T/$id/Model.lean"
  def obligationsModule(id: String): String = s"FrFlowGen.$T.$id.Obligations"
  def obligationsPath(id: String): String = s"FrFlowGen/$T/$id/Obligations.lean"
  def autoModule(id: String): String = s"FrFlowGen.$T.$id.Auto"
  def autoPath(id: String): String = s"FrFlowGen/$T/$id/Auto.lean"
  def assemblyModule(id: String): String = s"FrFlowGen.$T.$id.Assembly"
  def assemblyPath(id: String): String = s"FrFlowGen/$T/$id/Assembly.lean"
  def proofsModule(id: String): String = s"Proofs.$T.$id"
  def proofsPath(id: String): String = s"Proofs/$T/$id.lean"
  def auditPath(id: String): String = s"FrFlowAudit/$T/$id.lean"

  def generatedDirs: List[String] = List(s"FrFlowGen/$T", s"FrFlowAudit/$T")

  def renderAll: Map[String, String] =
    val theory = List(
      obligationsPath(TheoryId) -> renderTheoryObligations,
      autoPath(TheoryId) -> renderAuto(TheoryId),
      assemblyPath(TheoryId) -> renderTheoryAssembly,
      auditPath(TheoryId) -> renderAudit(TheoryId)
    )
    val layers = m.layers.flatMap { l =>
      List(
        modelPath(l.id) -> renderModel(l),
        obligationsPath(l.id) -> renderObligations(l),
        autoPath(l.id) -> renderAuto(l.id),
        assemblyPath(l.id) -> renderAssembly(l),
        auditPath(l.id) -> renderAudit(l.id)
      )
    }
    ((domainPath -> renderDomain) :: theory ++ layers).toMap

  def obligations(id: String): List[Obligation] =
    if id == TheoryId then Obligations.forTheory(m) else Obligations.forLayer(m, m.layerOrFail(id))

  // -- domain ------------------------------------------------------------------

  def renderDef(name: String): String =
    m.defs.adts.get(name).map(renderAdt).orElse(m.defs.funs.get(name).map(renderFun)).getOrElse("")

  def renderAdt(a: AdtDef): String =
    val sb = StringBuilder()
    sb ++= docComment(a.doc)
    a.shape match
      case AdtShape.Product(Nil) => sb ++= s"structure ${P.ident(a.name)}\n"
      case AdtShape.Product(fs) =>
        sb ++= s"structure ${P.ident(a.name)} where\n"
        fs.foreach { f =>
          if f.doc.nonEmpty then sb ++= s"  ${docComment(f.doc).trim}\n"
          sb ++= s"  ${P.segment(f.name)} : ${P.tpe(f.tpe)}\n"
        }
      case AdtShape.Sum(cs) =>
        sb ++= s"inductive ${P.ident(a.name)} where\n"
        cs.foreach { c =>
          if c.doc.nonEmpty then sb ++= s"  ${docComment(c.doc).trim}\n"
          val fields = c.fields.map(f => s" (${P.segment(f.name)} : ${P.tpe(f.tpe)})").mkString
          sb ++= s"  | ${P.segment(c.name)}$fields\n"
        }
    sb.result()

  def renderFun(f: FunDef): String =
    val params = if f.params.isEmpty then "" else " " + P.binders(f.params)
    docComment(f.doc) + s"@[frflow_defs] def ${P.ident(f.name)}$params : ${P.tpe(f.result)} :=${body(P.expr(f.body))}\n"

  def renderDomain: String =
    val sb = StringBuilder()
    sb ++= header(s"domain of theory $T, translated from its Scala ADTs and functions")
    sb ++= "import FrFlow\n\n"
    sb ++= Preamble
    sb ++= s"namespace $T\n\n"
    m.orderedDefs.foreach(n => sb ++= renderDef(n) ++= "\n")
    sb ++= s"end $T\n"
    sb.result()

  // -- theory: laws --------------------------------------------------------------

  def renderTheoryObligations: String =
    val sb = StringBuilder()
    sb ++= header(s"laws of theory $T as proof obligations")
    sb ++= s"import $domainModule\n\n"
    sb ++= Preamble
    sb ++= s"namespace $T.$TheoryId.Obl\n\n"
    obligations(TheoryId).foreach { o =>
      sb ++= docComment(o.description)
      sb ++= s"@[frflow_defs] def ${o.name} : Prop :=${body(o.statement)}\n\n"
    }
    sb ++= s"end $T.$TheoryId.Obl\n"
    sb.result()

  def renderTheoryAssembly: String =
    val sb = StringBuilder()
    sb ++= header(s"laws of theory $T as theorems")
    sb ++= s"import ${autoModule(TheoryId)}\n"
    if hasProofFile(TheoryId) then sb ++= s"import ${proofsModule(TheoryId)}\n"
    sb ++= "\n" + Preamble
    sb ++= s"namespace $T.Laws\n\n"
    obligations(TheoryId).foreach { o =>
      sb ++= docComment(o.description)
      sb ++= s"theorem ${o.name} :${body(o.statement)} :=\n  ${proofRef(TheoryId, o.name)}\n\n"
    }
    sb ++= s"end $T.Laws\n"
    sb.result()

  private def proofRef(node: String, obligation: String): String =
    val ns = if isAuthored(node, obligation) then "Proofs" else "Auto"
    s"$T.$node.$ns.$obligation"

  // -- layers ----------------------------------------------------------------------

  private def bodyOf(l: Lifted, names: String*): String = P.expr(l.bodyWith(names.toList))

  private def conj(parts: List[Expr]): String = parts match
    case Nil      => "True"
    case x :: Nil => P.expr(x)
    case xs       => xs.map(P.arg).mkString(" ∧ ")

  def renderModel(l: LayerModel): String =
    val sb = StringBuilder()
    val parent = m.parentOf(l)
    sb ++= header(s"model of layer ${l.id} (${l.name}), translated from its Scala definition")
    sb ++= s"import ${parent.fold(domainModule)(p => modelModule(p.id))}\n\n"
    sb ++= Preamble
    sb ++= s"namespace $T.${l.id}\n\n"
    sb ++= s"/-! # ${l.id} ${l.name} (${l.kind.label})\n\n${wrapComment(l.statement)}\n\nRationale: ${wrapComment(l.rationale)}\n-/\n\n"

    sb ++= s"abbrev State := ${P.tpe(l.stateType)}\n\n"
    val init = l.init match
      case Some(InitModel.Predicate(p)) => bodyOf(p, "s")
      case Some(InitModel.Value(v))     => s"s = ${P.arg(v.body)}"
      case None                         => "True"
    sb ++= s"@[frflow_defs] def Init (s : State) : Prop :=${body(init)}\n\n"

    if l.ops.nonEmpty then sb ++= "-- Operations\n\n"
    l.ops.foreach { op =>
      val o = P.segment(op.name)
      val pt = P.tpe(op.paramType)
      sb ++= docComment(op.doc)
      sb ++= s"@[frflow_defs] def $o.assume (s : State) (p : $pt) : Prop :=${body(conj(op.assumes.map(_.lifted.bodyWith(List("s", "p")))))}\n"
      sb ++= s"@[frflow_defs] def $o.check (s : State) (p : $pt) : Prop :=${body(conj(op.checks.map(_.bodyWith(List("s", "p")))))}\n"
      sb ++= s"@[frflow_defs] def $o.guard (s : State) (p : $pt) : Prop := $o.assume s p ∧ $o.check s p\n"
      sb ++= s"@[frflow_defs] def $o.act (s : State) (p : $pt) : State :=${body(op.act.fold("s")(a => bodyOf(a, "s", "p")))}\n"
      sb ++= s"def $o.event : FrFlow.Event State := ⟨$pt, $o.guard, $o.act⟩\n\n"
    }
    val evList = l.ops.map(op => s"${P.segment(op.name)}.event").mkString(", ")
    sb ++= s"def machine : FrFlow.Machine := ⟨State, Init, [$evList]⟩\n\n"

    if l.invariants.nonEmpty then
      sb ++= (if l.invariants.exists(_.requirement) then "-- Requirements and invariants\n\n" else "-- Invariants\n\n")
      l.invariants.foreach { i =>
        sb ++= docComment(i.doc)
        sb ++= s"@[frflow_defs] def ${P.segment(i.name)} (s : State) : Prop :=${body(bodyOf(i.lifted, "s"))}\n\n"
      }

    (parent, l.link) match
      case (Some(p), Some(link)) =>
        sb ++= s"-- Link to ${p.id}\n\n"
        sb ++= s"@[frflow_defs] def abs (s : State) : ${p.id}.State :=${body(bodyOf(link.abs, "s"))}\n\n"
        link.glue.foreach(g => sb ++= s"@[frflow_defs] def glue (s : State) : Prop :=${body(bodyOf(g, "s"))}\n\n")
        l.ops.foreach { op =>
          op.target match
            case TargetModel.Refines(_, ao, w) =>
              val parentOp = p.op(ao)
              val wt = parentOp.fold("_")(po => P.tpe(po.paramType))
              sb ++= s"@[frflow_defs] def ${P.segment(op.name)}.witness (s : State) (p : ${P.tpe(op.paramType)}) : $wt :=${body(bodyOf(w, "s", "p"))}\n\n"
            case _ => ()
        }
      case _ => ()

    sb ++= s"end $T.${l.id}\n"
    sb.result()

  def renderObligations(l: LayerModel): String =
    val sb = StringBuilder()
    val invs = Obligations.effectiveInvariants(l)
    sb ++= header(s"proof obligations of layer ${l.id} (${l.name})")
    sb ++= s"import ${modelModule(l.id)}\n\n"
    sb ++= Preamble
    sb ++= s"namespace $T.${l.id}.Obl\n\n"
    sb ++= "/-- Conjunction of the layer's invariants (gluing invariant first). -/\n"
    sb ++= s"@[frflow_defs] def Hyp (s : State) : Prop := ${if invs.isEmpty then "True" else invs.map(i => s"${P.segment(i.name)} s").mkString(" ∧ ")}\n\n"
    obligations(l.id).foreach { o =>
      sb ++= docComment(o.description)
      sb ++= s"@[frflow_defs] def ${o.name} : Prop :=\n  ${o.statement}\n\n"
    }
    sb ++= s"end $T.${l.id}.Obl\n"
    sb.result()

  /** Automation attempts for every obligation of a node that has no authored proof. */
  def renderAuto(id: String): String =
    val sb = StringBuilder()
    sb ++= header(s"automatic proofs (frflow_auto) for node $id")
    sb ++= s"import ${obligationsModule(id)}\n\n"
    sb ++= Preamble
    sb ++= s"namespace $T.$id.Auto\n"
    sb ++= s"open $T.$id\n\n"
    obligations(id).filterNot(o => isAuthored(id, o.name)).foreach { o =>
      sb ++= docComment(o.description)
      sb ++= s"theorem ${o.name} : Obl.${o.name} := by\n  unfold Obl.${o.name}\n  frflow_auto\n\n"
    }
    sb ++= s"end $T.$id.Auto\n"
    sb.result()

  /** Properties guaranteed at layer `l`: own invariants and everything inherited. */
  def guarantees(l: LayerModel): List[Guarantee] =
    val own = l.invariants.map(i => Guarantee(l.id, i.name, i.requirement, Nil))
    val inherited = m.parentOf(l).toList.flatMap(guarantees).map(g => g.copy(chain = l.id :: g.chain))
    own ++ inherited

  def renderAssembly(l: LayerModel): String =
    val sb = StringBuilder()
    val invs = Obligations.effectiveInvariants(l)
    val parent = m.parentOf(l)
    def ref(o: String): String = proofRef(l.id, o)
    sb ++= header(s"assembly of layer ${l.id}: kernel theorems built from the proofs")
    sb ++= s"import ${autoModule(l.id)}\n"
    if hasProofFile(l.id) then sb ++= s"import ${proofsModule(l.id)}\n"
    parent.foreach(p => sb ++= s"import ${assemblyModule(p.id)}\n")
    sb ++= "\n" + Preamble
    sb ++= s"namespace $T.${l.id}\n"
    sb ++= "open FrFlow\n\n"

    val initHyp = tuple(invs.map(i => s"${ref(s"init_${i.name}")} s h"))
    def opHyp(o: String): String =
      if invs.isEmpty then "fun _ _ _ _ => trivial"
      else s"fun s p h g => ${tuple(invs.map(i => s"${ref(s"${o}_inv_${i.name}")} s p h g"))}"

    parent match
      case None =>
        sb ++= "theorem invariant : Invariant machine.toSpec Obl.Hyp :=\n"
        sb ++= "  Machine.invariant machine Obl.Hyp\n"
        sb ++= s"    (fun s h => $initHyp)\n"
        val items = l.ops.map(op => opHyp(op.name)) :+ "trivial"
        sb ++= s"    ⟨${items.mkString(",\n     ")}⟩\n\n"
      case Some(p) =>
        sb ++= s"def refinement : Refinement machine.toSpec ${p.id}.machine.toSpec :=\n"
        sb ++= s"  Machine.refinement machine ${p.id}.machine abs Obl.Hyp\n"
        sb ++= s"    (fun s h => ⟨$initHyp, ${ref("init_abs")} s h⟩)\n"
        val items = l.ops.map { op =>
          val o = P.segment(op.name)
          op.target match
            case TargetModel.Refines(_, ao, _) =>
              val idx = p.ops.indexWhere(_.name == ao)
              s"EventSim.refines ${p.id}.${P.segment(ao)}.event ${memPath(idx)} $o.witness\n" +
                s"       (${opHyp(op.name)})\n" +
                s"       ${ref(s"${op.name}_grd")} ${ref(s"${op.name}_sim")}"
            case _ =>
              s"EventSim.skip (${opHyp(op.name)}) ${ref(s"${op.name}_skip")}"
        } :+ "trivial"
        sb ++= s"    ⟨${items.mkString(",\n     ")}⟩\n\n"
        sb ++= "theorem invariant : Invariant machine.toSpec Obl.Hyp := refinement.invariant\n\n"

    l.invariants.foreach { i =>
      val j = invs.indexWhere(_.name == i.name)
      sb ++= s"theorem ${i.name}_holds : Invariant machine.toSpec ${P.segment(i.name)} :=\n"
      sb ++= s"  fun s hr => (invariant s hr)${projection(j, invs.size)}\n\n"
    }

    guarantees(l).filterNot(_.isOwn).foreach { g =>
      val parentThm = Guarantee(g.origin, g.invariant, g.requirement, g.chain.tail).theoremName
      val what = if g.requirement then "requirement" else "invariant"
      sb ++= s"/-- Inherited from ${g.origin}: $what ${g.invariant}. -/\n"
      sb ++= s"theorem ${g.theoremName.stripPrefix(l.id + ".")} : Invariant machine.toSpec (${g.predicate}) :=\n"
      sb ++= s"  refinement.transfer $parentThm\n\n"
    }

    sb ++= s"end $T.${l.id}\n"
    sb.result()

  /** Fully qualified names of the theorems the audit checks for a node. */
  def auditedTheorems(id: String): List[String] =
    if id == TheoryId then obligations(TheoryId).map(o => s"$T.Laws.${o.name}")
    else
      val l = m.layerOrFail(id)
      val main = if l.isRoot then s"$T.${l.id}.invariant" else s"$T.${l.id}.refinement"
      main :: guarantees(l).map(g => s"$T.${g.theoremName}")

  def renderAudit(id: String): String =
    val sb = StringBuilder()
    sb ++= header(s"axiom audit of node $id")
    sb ++= s"import ${assemblyModule(id)}\n\n"
    auditedTheorems(id).foreach(t => sb ++= s"#print axioms $t\n")
    sb.result()

  // -- authored proofs -------------------------------------------------------------

  def proofFileHeader(id: String): String =
    s"""import ${obligationsModule(id)}
       |
       |/-!
       |Authored proofs for node $id of theory $T.
       |
       |Only obligations that `frflow_auto` does not prove need a theorem here.
       |Write `theorem <name> : Obl.<name>`; the statement must be exactly `Obl.<name>`.
       |An obligation proven here is no longer attempted automatically.
       |-/
       |
       |set_option autoImplicit false
       |noncomputable section
       |open Classical FrFlow
       |
       |namespace $T.$id.Proofs
       |open $T.$id
       |
       |""".stripMargin

  def proofFileFooter(id: String): String = s"end $T.$id.Proofs\n"

  def proofStub(o: Obligation): String =
    s"""/-- ${o.description} -/
       |theorem ${o.name} : Obl.${o.name} := by
       |  unfold Obl.${o.name}
       |  sorry
       |
       |""".stripMargin

object LeanRenderer:

  val Preamble: String =
    "set_option autoImplicit false\nset_option linter.unusedVariables false\nnoncomputable section\nopen Classical FrFlow\n\n"

  def header(what: String): String =
    s"-- GENERATED by FrFlow: $what.\n-- Do not edit. Change the Scala model and render again.\n\n"

  def docComment(doc: String): String =
    if doc.trim.isEmpty then "" else s"/-- ${wrapComment(doc.trim)} -/\n"

  /** Prevents user text from closing a Lean comment. */
  def wrapComment(text: String): String = text.replace("-/", "- /")

  /** A definition body: on the same line when short, indented on the next line otherwise. */
  def body(expr: String): String =
    val t = expr.trim
    if t.length <= 60 && !t.contains('\n') then " " + t
    else "\n" + t.linesIterator.map("  " + _).mkString("\n")

  /** A right-nested conjunction proof from component proofs. */
  def tuple(parts: List[String]): String = parts match
    case Nil      => "trivial"
    case x :: Nil => x
    case xs       => xs.mkString("⟨", ", ", "⟩")

  /** Projection of the j-th conjunct of a right-nested conjunction of size k. */
  def projection(j: Int, k: Int): String =
    if k <= 1 then ""
    else if j == k - 1 then ".2" * j
    else ".2" * j + ".1"

  /** Proof term of `List.Mem` for the element at index `idx`. */
  def memPath(idx: Int): String =
    require(idx >= 0, "operation index must be non-negative")
    (0 until idx).foldLeft("(List.Mem.head _)")((acc, _) => s"(List.Mem.tail _ $acc)")

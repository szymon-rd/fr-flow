package frflow.render

import frflow.model.*
import frflow.obligation.{Obligation, Obligations, ObligationKind}

/** One property guaranteed at a node: either declared on the node itself, or
  * inherited from an ancestor through the chain of abstraction functions.
  *
  * @param origin    node that declares the invariant
  * @param invariant invariant name
  * @param chain     node ids from the guaranteeing node up to (excluding) `origin`;
  *                  empty for the node's own invariants
  */
final case class Guarantee(origin: String, invariant: String, chain: List[String]):
  def isOwn: Boolean = chain.isEmpty

  /** Name of the theorem proving this guarantee, relative to the theory namespace. */
  def theoremName: String = chain.headOption match
    case None       => s"$origin.${invariant}_holds"
    case Some(node) => s"$node.inherits_${origin}_$invariant"

  /** Lean predicate over the guaranteeing node's state. */
  def predicate: String =
    if isOwn then invariant
    else s"fun s => $origin.$invariant (${chain.foldLeft("s")((acc, id) => s"$id.abs ($acc)")})"

/** Renders a theory to Lean source files.
  *
  * Layout, relative to the Lean workspace:
  *   - `FrFlowGen/<Theory>/Vocab.lean`
  *   - `FrFlowGen/<Theory>/<Node>/Model.lean`        model, link to parent
  *   - `FrFlowGen/<Theory>/<Node>/Obligations.lean`  obligation statements
  *   - `FrFlowGen/<Theory>/<Node>/Assembly.lean`     kernel theorems built from proofs
  *   - `FrFlowAudit/<Theory>/<Node>.lean`            axiom audit script (not a library module)
  *
  * Authored proofs live in `Proofs/<Theory>/<Node>.lean` and are never written by
  * the renderer, except by `scaffold`, which only creates or appends.
  */
final class LeanRenderer(theory: TheoryModel):
  import LeanRenderer.*

  private val T = theory.name

  def modelModule(n: Node): String = s"FrFlowGen.$T.${n.id}.Model"
  def obligationsModule(n: Node): String = s"FrFlowGen.$T.${n.id}.Obligations"
  def assemblyModule(n: Node): String = s"FrFlowGen.$T.${n.id}.Assembly"
  def proofsModule(n: Node): String = s"Proofs.$T.${n.id}"
  def vocabModule: String = s"FrFlowGen.$T.Vocab"

  def modelPath(n: Node): String = s"FrFlowGen/$T/${n.id}/Model.lean"
  def obligationsPath(n: Node): String = s"FrFlowGen/$T/${n.id}/Obligations.lean"
  def assemblyPath(n: Node): String = s"FrFlowGen/$T/${n.id}/Assembly.lean"
  def proofsPath(n: Node): String = s"Proofs/$T/${n.id}.lean"
  def auditPath(n: Node): String = s"FrFlowAudit/$T/${n.id}.lean"
  def vocabPath: String = s"FrFlowGen/$T/Vocab.lean"

  /** Root directory of generated files for this theory, relative to the workspace. */
  def generatedDirs: Seq[String] = Seq(s"FrFlowGen/$T", s"FrFlowAudit/$T")

  /** All generated files, keyed by workspace-relative path. */
  def renderAll: Map[String, String] =
    val perNode = theory.nodes.flatMap { n =>
      Seq(
        modelPath(n) -> renderModel(n),
        obligationsPath(n) -> renderObligations(n),
        assemblyPath(n) -> renderAssembly(n),
        auditPath(n) -> renderAudit(n)
      )
    }
    (perNode :+ (vocabPath -> renderVocab)).toMap

  // -------------------------------------------------------------------------
  // Vocabulary
  // -------------------------------------------------------------------------

  def renderVocab: String =
    val sb = StringBuilder()
    sb ++= header(s"vocabulary of theory $T")
    sb ++= "import FrFlow\n\n"
    sb ++= s"namespace $T\n\n"
    theory.vocabulary.foreach {
      case VocabEntry.Opaque(name, doc) =>
        sb ++= docComment(doc)
        sb ++= s"opaque $name : Type\n\n"
      case VocabEntry.Alias(name, lean, doc) =>
        sb ++= docComment(doc)
        sb ++= s"abbrev $name := ${lean.text}\n\n"
    }
    sb ++= s"end $T\n"
    sb.result()

  // -------------------------------------------------------------------------
  // Model
  // -------------------------------------------------------------------------

  def renderModel(n: Node): String =
    val sb = StringBuilder()
    val parent = theory.parentOf(n)
    sb ++= header(s"model of node ${n.id} (${n.name})")
    sb ++= s"import ${parent.fold(vocabModule)(modelModule)}\n\n"
    sb ++= Preamble
    sb ++= s"namespace $T.${n.id}\n\n"
    sb ++= s"/-! # ${n.id} ${n.name}\n\n${wrapComment(n.statement)}\n\nRationale: ${wrapComment(n.rationale)}\n-/\n\n"

    if n.spec.defs.nonEmpty then
      sb ++= "-- Definitions\n\n"
      n.spec.defs.foreach(d => sb ++= d.text ++= "\n\n")

    sb ++= "-- State\n\n"
    sb ++= "structure State where\n"
    n.spec.state.foreach { f =>
      if f.doc.nonEmpty then sb ++= s"  /-- ${f.doc} -/\n"
      sb ++= s"  ${f.name} : ${f.tpe.text}\n"
    }
    sb ++= "\n"
    sb ++= s"def Init (s : State) : Prop :=${body(n.spec.init.text)}\n\n"

    sb ++= "-- Events\n\n"
    n.spec.events.foreach { e =>
      val ev = e.name
      if e.description.nonEmpty then sb ++= docComment(e.description)
      sb ++= s"structure $ev.Params where\n"
      e.parameters.foreach(f => sb ++= s"  ${f.name} : ${f.tpe.text}\n")
      sb ++= "\n"
      sb ++= s"def $ev.assume (s : State) (p : $ev.Params) : Prop :=${body(conj(e.assumes.map(_.expr.text)))}\n"
      sb ++= s"def $ev.check (s : State) (p : $ev.Params) : Prop :=${body(conj(e.checks.map(_.text)))}\n"
      sb ++= s"def $ev.guard (s : State) (p : $ev.Params) : Prop := $ev.assume s p ∧ $ev.check s p\n"
      sb ++= s"def $ev.act (s : State) (p : $ev.Params) : State :=${body(e.action.fold("s")(_.text))}\n"
      sb ++= s"def $ev.event : FrFlow.Event State := ⟨$ev.Params, $ev.guard, $ev.act⟩\n\n"
    }
    val evList = n.spec.events.map(e => s"${e.name}.event").mkString(", ")
    sb ++= s"def machine : FrFlow.Machine := ⟨State, Init, [$evList]⟩\n\n"

    if n.spec.invariants.nonEmpty then
      sb ++= "-- Invariants\n\n"
      n.spec.invariants.foreach { i =>
        if i.doc.nonEmpty then sb ++= docComment(i.doc)
        sb ++= s"def ${i.name} (s : State) : Prop :=${body(i.expr.text)}\n\n"
      }

    (parent, n.link) match
      case (Some(p), Some(l)) =>
        sb ++= s"-- Link to ${p.id}\n\n"
        sb ++= s"def abs (s : State) : ${p.id}.State :=${body(l.abs.text)}\n\n"
        l.glue.foreach(g => sb ++= s"def glue (s : State) : Prop :=${body(g.text)}\n\n")
        n.spec.events.foreach { e =>
          e.target match
            case EventTarget.Refines(ae, w) =>
              sb ++= s"def ${e.name}.witness (s : State) (p : ${e.name}.Params) : ${p.id}.$ae.Params :=${body(w.text)}\n\n"
            case _ => ()
        }
      case _ => ()

    sb ++= s"end $T.${n.id}\n"
    sb.result()

  // -------------------------------------------------------------------------
  // Obligations
  // -------------------------------------------------------------------------

  def obligations(n: Node): Seq[Obligation] = Obligations.forNode(theory, n)

  def renderObligations(n: Node): String =
    val sb = StringBuilder()
    val invs = Obligations.effectiveInvariants(n)
    sb ++= header(s"proof obligations of node ${n.id} (${n.name})")
    sb ++= s"import ${modelModule(n)}\n\n"
    sb ++= Preamble
    sb ++= s"namespace $T.${n.id}.Obl\n\n"
    sb ++= "/-- Conjunction of all invariants of the node (gluing invariant first). -/\n"
    sb ++= s"def Hyp (s : State) : Prop := ${conj(invs.map(i => s"${i.leanRef} s"))}\n\n"
    obligations(n).foreach { o =>
      sb ++= docComment(o.description)
      sb ++= s"def ${o.name} : Prop :=\n  ${o.statement}\n\n"
    }
    sb ++= s"end $T.${n.id}.Obl\n"
    sb.result()

  // -------------------------------------------------------------------------
  // Assembly
  // -------------------------------------------------------------------------

  /** Properties guaranteed at node `n`: own invariants and everything inherited. */
  def guarantees(n: Node): Seq[Guarantee] =
    val own = n.spec.invariants.map(i => Guarantee(n.id, i.name, Nil))
    val inherited = theory.parentOf(n).toSeq.flatMap(guarantees).map(g => g.copy(chain = n.id :: g.chain))
    own ++ inherited

  def renderAssembly(n: Node): String =
    val sb = StringBuilder()
    val invs = Obligations.effectiveInvariants(n)
    val parent = theory.parentOf(n)
    sb ++= header(s"assembly of node ${n.id}: kernel theorems built from the proofs")
    sb ++= s"import ${obligationsModule(n)}\n"
    parent.foreach(p => sb ++= s"import ${assemblyModule(p)}\n")
    sb ++= s"import ${proofsModule(n)}\n\n"
    sb ++= Preamble
    sb ++= s"namespace $T.${n.id}\n"
    sb ++= "open FrFlow\n\n"

    val initHyp = tuple(invs.map(i => s"Proofs.init_${i.name} s h"))
    def evHyp(ev: String): String =
      if invs.isEmpty then "fun _ _ _ _ => trivial"
      else s"fun s p h g => ${tuple(invs.map(i => s"Proofs.${ev}_inv_${i.name} s p h g"))}"

    parent match
      case None =>
        sb ++= "theorem invariant : Invariant machine.toSpec Obl.Hyp :=\n"
        sb ++= "  Machine.invariant machine Obl.Hyp\n"
        sb ++= s"    (fun s h => $initHyp)\n"
        val items = n.spec.events.map(e => evHyp(e.name)) :+ "trivial"
        sb ++= s"    ⟨${items.mkString(",\n     ")}⟩\n\n"
      case Some(p) =>
        sb ++= s"def refinement : Refinement machine.toSpec ${p.id}.machine.toSpec :=\n"
        sb ++= s"  Machine.refinement machine ${p.id}.machine abs Obl.Hyp\n"
        sb ++= s"    (fun s h => ⟨$initHyp, Proofs.init_abs s h⟩)\n"
        val items = n.spec.events.map { e =>
          e.target match
            case EventTarget.Refines(ae, _) =>
              val idx = p.spec.events.indexWhere(_.name == ae)
              s"EventSim.refines ${p.id}.$ae.event ${memPath(idx)} ${e.name}.witness\n" +
                s"       (${evHyp(e.name)})\n" +
                s"       Proofs.${e.name}_grd Proofs.${e.name}_sim"
            case _ =>
              s"EventSim.skip (${evHyp(e.name)}) Proofs.${e.name}_skip"
        } :+ "trivial"
        sb ++= s"    ⟨${items.mkString(",\n     ")}⟩\n\n"
        sb ++= "theorem invariant : Invariant machine.toSpec Obl.Hyp := refinement.invariant\n\n"

    n.spec.invariants.foreach { i =>
      val j = invs.indexWhere(_.name == i.name)
      sb ++= s"theorem ${i.name}_holds : Invariant machine.toSpec ${i.name} :=\n"
      sb ++= s"  fun s hr => (invariant s hr)${projection(j, invs.size)}\n\n"
    }

    guarantees(n).filterNot(_.isOwn).foreach { g =>
      val parentThm = parent.map(p => guaranteeAtParent(p, g)).get
      sb ++= s"/-- Inherited from ${g.origin}: ${g.invariant}. -/\n"
      sb ++= s"theorem ${g.theoremName.stripPrefix(n.id + ".")} : Invariant machine.toSpec (${g.predicate}) :=\n"
      sb ++= s"  refinement.transfer $parentThm\n\n"
    }

    sb ++= s"end $T.${n.id}\n"
    sb.result()

  /** Theorem name, at the parent, of the guarantee that `g` (at the child) inherits. */
  private def guaranteeAtParent(parent: Node, g: Guarantee): String =
    Guarantee(g.origin, g.invariant, g.chain.tail).theoremName

  /** Fully qualified names of the theorems the audit checks for node `n`. */
  def auditedTheorems(n: Node): Seq[String] =
    val main = if n.isRoot then s"$T.${n.id}.invariant" else s"$T.${n.id}.refinement"
    main +: guarantees(n).map(g => s"$T.${g.theoremName}")

  def renderAudit(n: Node): String =
    val sb = StringBuilder()
    sb ++= header(s"axiom audit of node ${n.id}")
    sb ++= s"import ${assemblyModule(n)}\n\n"
    auditedTheorems(n).foreach(t => sb ++= s"#print axioms $t\n")
    sb.result()

  // -------------------------------------------------------------------------
  // Proof scaffold
  // -------------------------------------------------------------------------

  def proofFileHeader(n: Node): String =
    s"""import ${obligationsModule(n)}
       |
       |/-!
       |Proofs of the obligations of node ${n.id} (${n.name}).
       |
       |Authored file: write one `theorem <name> : Obl.<name>` per obligation.
       |The statement after the colon must be exactly `Obl.<name>`.
       |-/
       |
       |namespace $T.${n.id}.Proofs
       |open $T.${n.id}
       |
       |""".stripMargin

  def proofFileFooter(n: Node): String = s"end $T.${n.id}.Proofs\n"

  def proofStub(o: Obligation): String =
    s"""/-- ${o.description} -/
       |theorem ${o.name} : Obl.${o.name} := by
       |  sorry
       |
       |""".stripMargin

object LeanRenderer:

  val Preamble: String =
    "set_option linter.unusedVariables false\nset_option autoImplicit false\n\n"

  def header(what: String): String =
    s"-- GENERATED by FrFlow: $what.\n-- Do not edit. Change the theory definition and re-render.\n\n"

  def docComment(doc: String): String =
    if doc.trim.isEmpty then "" else s"/-- ${wrapComment(doc.trim)} -/\n"

  /** Prevents user text from closing a Lean comment. */
  def wrapComment(text: String): String = text.replace("-/", "- /")

  /** Renders a definition body: inline when single-line, indented otherwise. */
  def body(expr: String): String =
    val t = expr.trim
    if t.contains('\n') then "\n" + t.linesIterator.map("  " + _).mkString("\n")
    else " " + t

  def conj(parts: Seq[String]): String =
    parts.map(_.trim).filter(_.nonEmpty) match
      case Seq()  => "True"
      case Seq(x) => paren(x)
      case xs     => xs.map(paren).mkString(" ∧ ")

  /** A right-nested conjunction proof from component proofs. */
  def tuple(parts: Seq[String]): String = parts match
    case Seq()  => "trivial"
    case Seq(x) => x
    case xs     => xs.mkString("⟨", ", ", "⟩")

  /** Projection of the j-th conjunct of a right-nested conjunction of size k. */
  def projection(j: Int, k: Int): String =
    if k <= 1 then ""
    else if j == k - 1 then ".2" * j
    else ".2" * j + ".1"

  /** Proof term of `List.Mem` for the element at index `idx`. */
  def memPath(idx: Int): String =
    require(idx >= 0, "event index must be non-negative")
    (0 until idx).foldLeft("(List.Mem.head _)")((acc, _) => s"(List.Mem.tail _ $acc)")

  private def paren(x: String): String =
    if isAtomic(x) then x else s"($x)"

  private def isAtomic(x: String): Boolean =
    x == "True" || x == "False" || x.matches("""[A-Za-z_][A-Za-z0-9_.']*""")

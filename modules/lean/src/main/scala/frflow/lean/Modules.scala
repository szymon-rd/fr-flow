package frflow
package lean

import frflow.protocol.{ObligationName, TryKind}
import scala.collection.immutable.ListSet
import ObligationName.*
import LeanText.*

/** The vocabulary, a module per `define` and per defined term: a change to one rebuilds only the nodes that use it. */
final class VocabularyModules(kb: KnowledgeBase, layout: Layout, vocabulary: Vocabulary):
  import vocabulary.*
  private val K = kb.name

  def types: String =
    val abbrevs = definitionsInForce.collect { case (t, d, s) if s.isType => s"/-- ${d.id} -/\n@[frflow_defs] abbrev $t : Type := ${s.lean}" }
    module(List(LeanModule("FrFlow")), K, (kb.types.map(_.lean) ++ abbrevs).mkString("\n\n") + "\n\n")
  private def declaring(uses: List[LeanModule], decl: String): String =
    module((layout.types :: uses).distinct, K, decl + "\n\n" + MatchEqns + "\n")
  private def definedTerms: List[(String, Node[?], Lifted[?])] =
    definitionsInForce.collect { case (t, d, s) if !s.isType => s.term.map((t, d, _)) }.flatten

  /** A module that mentions the boundaries' world or calls a boundary imports them. */
  def boundariesFor(ls: List[Lifted[?]]): List[LeanModule] =
    Option.when(ls.exists(l => l.world || l.boundaries.nonEmpty))(layout.boundaries).toList

  def files: List[(String, String)] =
    val defs = kb.defs.map { d =>
      // A flow is generic in its monad: any with the boundaries' operations.
      val (monad, tpe) =
        if d.isFlow then (s"{m : Type → Type} [Monad m]${d.lifted.boundaries.map(b => s" [${b.lean} m]").mkString}",
          (d.lifted.params.map(_._2) :+ s"m ${d.lifted.result}").mkString(" → "))
        else ("", d.lifted.leanType)
      val uses = boundariesFor(List(d.lifted)) ++ d.lifted.defs.map(_.name).filter(x => x != d.name && defNames(x)).map(layout.definition)
      layout.definition(d.name).path -> declaring(uses,
        definition(d.name, List(monad, binders(defCtx(d))).filter(_.nonEmpty).mkString(" "), tpe, resolve(d.lifted.lean)))
    }
    val terms = definedTerms.map { (t, d, l) =>
      layout.term(t).path -> declaring(l.defs.map(_.name).filter(defNames).map(layout.definition),
        s"/-- ${d.id} -/\n" + definition(t, binders(ctx(l)), l.leanType, resolve(l.lean)))
    }
    defs ++ terms

  def domainModule: String =
    Header + imports((layout.types :: kb.defs.map(d => layout.definition(d.name)) ++ definedTerms.map(t => layout.term(t._1))).distinct)
  def domain: String = (types :: files.map(_._2)).mkString("\n")

  private final case class Needs(defs: ListSet[String], terms: ListSet[String]):
    def define(d: Def[?]): Needs = Def.closure(List(d)).foldLeft(this) { (acc, x) =>
      if !defNames(x.name) || acc.defs(x.name) then acc
      else defCtx(x).names.foldLeft(acc.copy(defs = acc.defs + x.name))(_.term(_))
    }
    def term(t: String): Needs = definedTerm(t) match
      case Some(l) if !terms(t) =>
        val withDefs = l.defs.foldLeft(copy(terms = terms + t))(_.define(_))
        ctx(l).names.foldLeft(withDefs)(_.term(_))
      case _ => this

  def modulesFor(defs: List[Def[?]], terms: List[String]): List[LeanModule] =
    val needs = terms.foldLeft(defs.foldLeft(Needs(ListSet.empty, ListSet.empty))(_.define(_)))(_.term(_))
    needs.defs.toList.map(layout.definition) ++ needs.terms.toList.map(layout.term)

/** The Lean modules of each formal node: its model and the theorems proven of it. */
final class NodeModules(kb: KnowledgeBase, layout: Layout, refinement: Refinement, vocabularyModules: VocabularyModules,
    obligations: Obligations, evals: Evals):
  import refinement.*
  import refinement.vocabulary.*
  import obligations.*
  private val K = kb.name

  private def vocabularyOf(n: Node[?]): List[LeanModule] =
    val ls = n.referenced ++ formalKeeps(n).flatMap(_._1.rule)
    val code = provenImpl(n).toList
    vocabularyModules.boundariesFor(ls ++ code.map(_.lifted)) ++
      vocabularyModules.modulesFor(ls.flatMap(_.defs) ++ code, ls.flatMap(ctx(_).names) ++ code.flatMap(defCtx(_).names) ++ n.op.map(_.name))
  private def declared(name: String, c: Ctx, tpe: String, body: String): String = definition(name, binders(c), tpe, body) + "\n\n"
  private def lifted(name: String, l: Lifted[?]): String = declared(name, ctx(l), l.leanType, resolve(l.lean))

  /** `∀ inputs, what inputs (op inputs) rest`, of every call of `c`'s operation; of a flow's, every run from every world:
    * `∀ a w, post a (op a w).1 w (op a w).2`.
    */
  private def everyCall(c: Node[?], what: String, rest: String = ""): String =
    c.post.zip(c.op).fold("True") { (p, op) =>
      if c.isFlow then
        val List(a, _, w, _) = p.params.map(_._2): @unchecked
        val run = s"(${op.name} x0 x1)"
        s"∀ (x0 : $a) (x1 : $w), $what x0 $run.1 x1 $run.2$rest"
      else
        val (vars, xs) = call(p.params.init.map(_._2))
        s"∀ $vars, $what $xs (${op.name} $xs)$rest"
    }

  private def model(n: Node[?]): List[String] = (n.rule, n.post) match
    case (Some(r), _) =>
      val ks = keepers(n)
      val rule = ref(qualified(n, "rule"), ctx(r))
      val claim = if ks.isEmpty then "True" else ks.map((c, v) => keeps(n, c, v, rule)).mkString(" ∧ ")
      List(lifted("rule", r)) ++ ks.map((c, v) => lifted(s"view_${c.id}", v)) ++ List(declared("claim", claimCtx(n), "Prop", claim))
    case (_, Some(post)) =>
      val kept = formalKeeps(n).flatMap((inv, v) => inv.rule.toList.map(lifted(s"rule_${inv.id}", _)) :+ lifted(s"view_${inv.id}", v))
      List(lifted("post", post)) ++ kept ++ n.local.map(lifted("runCheck", _)) ++
        List(declared("claim", claimCtx(n), "Prop", everyCall(n, ref(qualified(n, "post"), ctx(post)))))
    case _ => n.formula.map(lifted("claim", _)).toList ++ conjunctsOf(n).zipWithIndex.map((c, i) =>
      doc(s"Conjunct ${i + 1} of the claim: a part that says only this restates it.") + declared(s"conjunct_${i + 1}", claimCtx(n), "Prop", resolve(c)))
  private def keeps(n: Node[?], c: Node[?], view: Lifted[?], rule: String): String =
    s"(${everyCall(c, s"∀ p ∈ ${ref(qualified(n, s"view_${c.id}"), ctx(view))}", s", $rule p.1 p.2")})"

  def spec(n: Node[?]): String =
    val uses = (layout.types :: vocabularyOf(n) ++ (kb.parts(n).filter(formal) ++ callees(n) ++ keepers(n).map(_._1)).map(c => layout.spec(c.id))).distinct
    val expected = n.expected.zipWithIndex.map { case ((_, l), i) => lifted(s"expected_$i", l) }
    val obls = (obligations.obligations(n) ++ tries(n).map(_.obligation)).map { o =>
      s"namespace Obl\n\n${doc(o.description)}@[frflow_defs] def ${o.name} : Prop :=\n  ${o.statement}\n\nend Obl\n\n"
    }
    module(uses, s"$K.${n.id}", (model(n) ++ expected ++ obls).mkString + MatchEqns + "\n")

  private def ownDefs(n: Node[?]): List[String] =
    qualified(n, "claim") :: (if n.isInvariant then qualified(n, "rule") :: keepers(n).map(k => qualified(n, s"view_${k._1.id}"))
      else if n.post.isDefined then List(qualified(n, "post")) else Nil)

  /** `complete`: first by matching the node's conjuncts among its parts' (seconds where `frflow_auto` times out). */
  def auto(n: Node[?]): String =
    val body = splitParts(n).filterNot(_ => isAuthored(n, Complete)).fold("") { ps =>
      val hs = ps.map(p => s"h_${p.id}").mkString(" ")
      val names = splitOpens(n, ps).names
      // A defined term the node mentions and none of its parts does names what its parts say together (a
      // group's): unfolded too. The terms its parts mention stay folded, as they state them.
      def mentions(x: Node[?]) = x.referenced.flatMap(ctx(_).names).toSet
      val below = ps.flatMap(mentions).toSet
      val groups = mentions(n).toList.sorted.filter(t => !below(t) && definitionOf(t).exists(!_.isType)).map(t => s"$K.$t")
      val defs = ((n :: ps).flatMap(ownDefs) ++ groups).distinct.mkString(", ")
      s"""set_option linter.unusedSimpArgs false in
         |theorem complete : Obl.complete := by
         |  unfold Obl.complete
         |  first
         |    | (intro ${(names :+ hs).mkString(" ")}
         |       simp only [$defs, List.forall_mem_map, forall_and] at $hs ⊢
         |       revert $hs
         |       try simp only [and_imp]
         |       repeat' (first | (with_reducible assumption) | (with_reducible intro _) | (with_reducible apply And.intro))
         |       done)
         |    | frflow_auto
         |
         |""".stripMargin
    }
    module(List(layout.spec(n.id)), s"$K.${n.id}.Auto", body, Some(s"$K.${n.id}"))

  def impl(n: Node[?]): String =
    val ns = s"$K.${n.id}.Impl"
    val (uses, proof) = if isAuthored(n, Impl) then (layout.proofs(n.id), s"$K.${n.id}.Proofs.impl") else (layout.spec(n.id), byAuto(Impl))
    module(List(uses), ns, s"theorem impl : Obl.impl :=\n  $proof\n\n#print axioms $ns.impl\n\n", Some(s"$K.${n.id}"))

  def theorems(n: Node[?]): String =
    val authoredSplit = isAuthored(n, Complete)
    val (uses, proof) = splitParts(n).fold((List(layout.spec(n.id)), s"h_${n.id}")) { ps =>
      val split = qualified(n, if authoredSplit then "Proofs.complete" else "Auto.complete")
      ((if authoredSplit then layout.proofs(n.id) else layout.auto(n.id)) :: ps.filterNot(leafy).map(c => layout.theorems(c.id)),
        s"$split ${named(splitOpens(n, ps))} ${ps.map(c => s"(h_${c.id} := ${proofOf(c)})").mkString(" ")}")
    }
    val intro = holdsOpens(n).names ++ leaves(n).map(l => s"h_${l.id}")
    module(uses, s"$K.${n.id}", s"/-- ${n.id} holds of every world that meets the leaves below it: ${leaves(n).map(_.id).mkString(", ")}. -/\n" +
      s"theorem $Holds : ${holdsStatement(n)} := by\n${introduce(intro)}  exact $proof\n\n")

  /** Elaborated, not built, each theorem on its own: the other obligations, the tries and `holds`' axioms. */
  def checks(n: Node[?]): String =
    val ns = s"$K.${n.id}.Checks"
    val extra = extraObligations(n)
    val uses = layout.theorems(n.id) :: Option.when(extra.exists(o => isAuthored(n, o.name)))(layout.proofs(n.id)).toList
    val proven = extra.map { o =>
      s"theorem ${o.name} : Obl.${o.name} := ${if isAuthored(n, o.name) then s"$K.${n.id}.Proofs.${o.name}" else byAuto(o.name)}\n\n#print axioms $ns.${o.name}\n\n"
    }
    val tried = tries(n).map { t =>
      val budget = if t.kind == TryKind.Idle then "" else s"set_option maxHeartbeats ${Generate.TryHeartbeats} in\n"
      s"${budget}theorem ${t.obligation.name} : Obl.${t.obligation.name} := ${byAuto(t.obligation.name)}\n\n"
    }
    module(uses, ns, (proven ++ tried).mkString + s"#print axioms $K.${n.id}.$Holds\n\n", Some(s"$K.${n.id}"))

  def evalFile(n: Node[?]): Option[String] =
    val es = evals.evals(n)._1
    Option.when(es.nonEmpty) {
      // Proven code's callees' specs hold the defines its world is computed with; without proven code, the defines do.
      val uses = layout.spec(n.id) :: provenImpl(n).fold(vocabularyModules.modulesFor(es.flatMap(_.defs).distinct, Nil))(_ =>
        callees(n).map(c => layout.spec(c.id)))
      module(uses, s"$K.${n.id}.Eval", es.map { e =>
        s"${doc(e.what)}theorem ${e.name} : ${e.claim} := by\n  frflow_eval\n\n" +
          s"theorem ${e.name}_opposite : ${e.opposite} := by\n  frflow_eval\n\n"
      }.mkString)
    }

  /** `root_impl`, composed of `holds` and `impl`: its statement, and the module. */
  def rootImpl: Option[(String, String)] = kb.root.filter(formal).map { r =>
    def proofIn(n: Node[?]): String = implementing(n).fold(s"h_${n.id}") { (d, op) =>
      s"(${qualified(n, "Impl.impl")} ${named(ofCode(n, d, op)._2, codeEnv)} ${calls(n).map(c => s"(h_${c.id} := ${proofIn(c)})").mkString(" ")})"
    }
    val implemented = kb.nodes.flatMap(n => implementing(n).map(n -> _))
    val hs = hyps(trusted, codeEnv)
    val (concl, co) = claim(r, codeEnv)
    // Every term the composition mentions once the code is in: the code's own inputs among them.
    val implOpens = implemented.map((n, impl) => Ctx.all(ofCode(n, impl._1, impl._2)._2.names.map(term(_, codeEnv)._2)))
    val opens = co ++ Ctx.all(hs.map(_._2)) ++ holdsOpens(r, codeEnv) ++ Ctx.all(implOpens)
    val statement = stated(opens, hs.map(_._1), concl)
    val intro = opens.names ++ trusted.map(t => s"h_${t.id}")
    val proof = s"by\n${introduce(intro)}  exact ${qualified(r, Holds)} ${named(holdsOpens(r), codeEnv)} " +
      leaves(r).map(l => s"(h_${l.id} := ${proofIn(l)})").mkString(" ")
    val uses = (layout.theorems(r.id) :: implemented.map((n, _) => layout.impl(n.id))).distinct
    (statement, module(uses, s"$K.RootImpl",
      s"/-- The root holds of the code, from what is trusted: ${if trusted.isEmpty then "nothing" else trusted.map(_.id).mkString(", ")}. -/\n" +
        s"theorem root_impl : $statement :=\n  $proof\n\n#print axioms $K.RootImpl.root_impl\n\n"))
  }
  private def introduce(names: List[String]): String = if names.isEmpty then "" else s"  intro ${names.mkString(" ")}\n"

/** The files proofs are written in (`Proofs/<KB>/<Node>.lean`), their stubs, and the Lake project. */
final class ProofFiles(kb: KnowledgeBase, layout: Layout, refinement: Refinement):
  private val K = kb.name

  /** For each obligation: the first steps of a proof by hand, what they leave (`state`), then `sorry`. */
  def stubs(names: List[ObligationName], state: ObligationName => String = _ => ""): String =
    names.map(o => s"theorem $o : Obl.$o := by\n  ${ProofFiles.recipe(o).mkString("\n  ")}\n${state(o)}  sorry\n\n").mkString

  def proofFile(n: Node[?], names: List[ObligationName] = List(Complete), state: ObligationName => String = _ => ""): String =
    val all = names ++ Option.when(names.contains(Complete) && !refinement.witnessed(n) && !names.contains(Feasible))(Feasible)
    s"""import ${layout.spec(n.id).name}
       |
       |/-! Authored proofs of the obligations of ${n.id}. Each states exactly its `Obl`. -/
       |
       |${Preamble}
       |namespace $K.${n.id}.Proofs
       |open $K.${n.id}
       |
       |""".stripMargin + stubs(all, state) + s"end $K.${n.id}.Proofs\n"

  /** A file whose unsolved goal Lean reports: what `o` leaves after the first steps of a proof by hand. */
  def goalFile(n: Node[?], o: ObligationName): String =
    val ns = s"$K.${n.id}"
    s"import ${layout.spec(n.id).name}\n\n${Preamble}namespace $ns.State\nopen $ns\n\ntheorem state : Obl.$o := by\n  " +
      ProofFiles.recipe(o).mkString("\n  ") + s"\n  done\n\nend $ns.State\n"

  def lakefile(kernelPath: String): String =
    s"name = \"${K.toLowerCase}\"\ndefaultTargets = [\"FrFlowGen\"]\n\n[[require]]\nname = \"frflow\"\npath = \"$kernelPath\"\n\n" +
      List("FrFlowGen", "Proofs").map(l => s"[[lean_lib]]\nname = \"$l\"\nglobs = [\"$l.+\"]\n").mkString("\n")

object ProofFiles:
  def recipe(o: ObligationName): List[String] = List(s"unfold Obl.$o", "frflow_intro", "simp only [frflow_defs] at *")

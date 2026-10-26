package frflow
package lean
package printing

import frflow.protocol.{ObligationName, TryKind}
import ObligationName.*
import LeanText.*

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
        // The post's binders: the inputs, the result, the world before and the world after.
        val ts = p.params.map(_._2)
        val ins = ts.dropRight(3)
        val (vars, xs) = call(ins :+ ts(ts.size - 2))
        val w = s"x${ins.size}"
        val args = ins.indices.map(i => s"x$i").mkString(" ")
        val run = s"(${op.name} $xs)"
        // A run that may fail: what holds of its outcome, the post of a result, the failure clause of an error.
        if c.failure.isDefined then
          val fail = c.failure.flatMap(_.post).fold(qualified(c, "failure"))(fp => ref(qualified(c, "failure"), ctx(fp)))
          s"∀ $vars, FrFlow.outcome (fun r' w' => $what ${if args.isEmpty then "" else args + " "}r' $w w') (fun e' w' => $fail e' $w w') $run$rest"
        else s"∀ $vars, $what ${if args.isEmpty then "" else args + " "}$run.1 $w $run.2$rest"
      else
        val (vars, xs) = call(p.params.init.map(_._2))
        // An operation of no inputs is a value: `what op`.
        if vars.isEmpty then s"$what ${op.name}$rest" else s"∀ $vars, $what $xs (${op.name} $xs)$rest"
    }

  private def model(n: Node[?]): List[String] = (n.rule, n.post) match
    case (Some(r), _) =>
      val ks = keepers(n)
      val rule = ref(qualified(n, "rule"), ctx(r))
      val claim = if ks.isEmpty then "True" else ks.map((c, v) => keeps(n, c, v, rule)).mkString(" ∧ ")
      List(lifted("rule", r)) ++ ks.map((c, v) => lifted(s"view_${c.id}", v)) ++ List(declared("claim", claimCtx(n), "Prop", claim))
    case (_, Some(post)) =>
      val kept = formalKeeps(n).flatMap((inv, v) => inv.rule.toList.map(lifted(s"rule_${inv.id}", _)) :+ lifted(s"view_${inv.id}", v))
      List(lifted("post", post)) ++ n.failure.map(failure(n, _)).toList ++ kept ++ n.local.map(lifted("runCheck", _)) ++
        List(declared("claim", claimCtx(n), "Prop", everyCall(n, ref(qualified(n, "post"), ctx(post)))))
    case _ => n.formula.map(lifted("claim", _)).toList ++ conjunctsOf(n).zipWithIndex.map((c, i) =>
      doc(s"Conjunct ${i + 1} of the claim: a part that says only this restates it.") + declared(s"conjunct_${i + 1}", claimCtx(n), "Prop", resolve(c)))
  /** What a contract on a flow says of a run that fails: its clause, or that every model's state is as before. */
  private def failure(n: Node[?], f: FailureClause): String = f.post.fold {
    val same = kb.models.map(m => s"w'.${m.model.field} = w.${m.model.field}")
    doc("A run that fails changes nothing: every model's state after it is as before.") +
      declared("failure", Ctx.empty, s"${frflow.Types.walk(f.err).lean} → World → World → Prop",
        s"fun (_ : ${frflow.Types.walk(f.err).lean}) (w w' : World) => ${if same.isEmpty then "True" else same.mkString(" ∧ ")}")
  }(lifted("failure", _))

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
    val (uses, proof) =
      if isAuthored(n, Impl) then (layout.proofs(n.id), s"$K.${n.id}.Proofs.impl")
      // A step of code: `impl` is `complete`, proven once.
      else if ofCodeStep(n) && isAuthored(n, Complete) then (layout.proofs(n.id), s"$K.${n.id}.Proofs.complete")
      else if ofCodeStep(n) then (layout.auto(n.id), s"$K.${n.id}.Auto.complete")
      else (layout.spec(n.id), byAuto(Impl))
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

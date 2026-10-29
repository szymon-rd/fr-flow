package frflow.proof.layout

import frflow.core.analysis.Resolved
import frflow.core.name.NodeId
import frflow.proof.lean.ast.*
import frflow.proof.lean.lower.{Atoms, LowerKeeps, LowerObligation, LowerType}
import frflow.proof.lean.term.{LeanTerm, Printed, Scope}
import frflow.proof.obligation.*
import frflow.proof.terms.{Conjoined, TermTable}

/** The modules of one node, from its obligations: `Spec` (its claim, each conjunct a try names, what `cover_` and
  * `made_` declare, and every obligation's statement), `Auto` (`complete` by automation), `Impl` (`impl`),
  * `Theorems` (`holds`: its claim from its leaves) and `Checks` (the other obligations and the tries within their
  * budget), each proof's axioms audited beside it. `Checks` imports no composition, so its obligations and tries are
  * judged whether or not `complete` goes through. An authored obligation's theorem is the proof file's.
  */
object NodeModules:
  def of(r: Resolved, table: TermTable, o: NodeObligations): List[LeanModule] = of(Lowering(r, table), o)

  def of(l: Lowering, o: NodeObligations): List[LeanModule] =
    List(Some(spec(l, o)), auto(l, o), impl(l, o), theorems(l, o), checks(l, o)).flatten

  private def module(l: Lowering, n: NodeId, part: NodePart, decls: List[Decl]): LeanModule =
    val name = l.layout.ofNode(n, part)
    val spec = Option.when(part != NodePart.Spec)(l.layout.ofNode(n, NodePart.Spec)).toList
    val namespace = if part == NodePart.Spec then Names.path(l.kb.value, n.value)
      else Names.path(l.kb.value, n.value, part.toString)
    val m = Imports.onto(l, LeanModule(name, Nil, Preamble.generated, namespace, Nil, decls))
    m.copy(imports = (m.imports ++ spec).distinct)

  private def spec(l: Lowering, o: NodeObligations): LeanModule =
    val said = l.resolved.theory.node(o.node).flatMap(_.statement.said)
    val rule = l.resolved.theory.node(o.node).exists(_.statement.rule)
    val params = claimParams(l, o.node)
    // A rule's claim is `True`: Lean has it of every value already, as a guard, and its `∀` over every value is false
    // of any rule some value breaks; what is asked of it is `cover_`, `made_`, `start_` and `inhabited_`.
    val claim = said.map(f => Decl.Def(defs, Names.builtin("claim"), params, Atoms.name("Prop"),
      if rule then Atoms.name("True")
      else Printed.claim(l.env, l.naming, l.guards(o.node), l.provided(o.node))(f.term)))
    val indices = o.tried.map(_.name).collect { case ObligationName.Tried(TryKind.RestatesConjunct(_, i)) => i }
    val conjuncts = said.toList.flatMap(f => Conjoined.of(f.term, LeanTerm(l.env)).zipWithIndex.collect {
      case (c, i) if indices.contains(i + 1) =>
        Decl.Def(defs, Names.builtin(s"conjunct_${i + 1}"), params, Atoms.name("Prop"), c(Scope(0, l.naming)))
    })
    val declared = o.required.flatMap(x => kept(x.goal)).flatMap(lowered(l, _))
    val obligations = (o.required ++ o.tried).map(LowerObligation(l.props)(_))
    module(l, o.node, NodePart.Spec, claim.toList ++ conjuncts ++ declared ++ obligations :+ Decl.MatchEqns)

  /** The binders of a node's claim: its opaque types, then its symbols, as `LowerProp` applies it. */
  private def claimParams(l: Lowering, n: NodeId): List[LBinder] =
    val terms = l.table.claims.getOrElse(n, frflow.proof.terms.OpenTerms.empty)
    Option.when(terms.sorts.nonEmpty)(LBinder.Several(terms.sorts.map(s => Names.ident(s.value)), Atoms.name("Type")))
      .toList ++ terms.symbols.map(s => LBinder.Explicit(Names.ident(s.value), LowerType.binder(l.table.typeOf(s))))

  /** What `cover_` and `made_` state: the `keeps_<op>` and `makes_<maker>` the statement applies. */
  private def kept(p: Prop): List[Prop] = p match
    case k: Prop.Keeps                                  => List(k)
    case m: Prop.Makes                                  => List(m)
    case Prop.Forall(_, b)                              => kept(b)
    case Prop.Implies(_, c)                             => kept(c)
    case _                                              => Nil

  private def lowered(l: Lowering, p: Prop): List[Decl] =
    val keeps = LowerKeeps(l.env, l.table, l.naming)
    val decl = p match
      case k: Prop.Keeps => List(keeps(k))
      case m: Prop.Makes => List(keeps.makes(m))
      case _             => Nil
    decl.flatMap {
      case Decl.Namespace(_, ds) => ds // declared in the node's own namespace: the `always`'s
      case other                 => List(other)
    }

  private def auto(l: Lowering, o: NodeObligations): Option[LeanModule] =
    o.required.find(x => x.name == ObligationName.Complete && x.discharge == Discharge.Auto).map(x =>
      module(l, o.node, NodePart.Auto, List(theorem(l, o.node, x))))

  private def impl(l: Lowering, o: NodeObligations): Option[LeanModule] =
    o.required.find(_.name == ObligationName.Impl).map(x => module(l, o.node, NodePart.Impl,
      List(theorem(l, o.node, x), audit(l, o.node, NodePart.Impl, "impl"))))

  private def theorems(l: Lowering, o: NodeObligations): Option[LeanModule] =
    val c = Composition(l)
    o.required.find(_.name == ObligationName.Complete).filter(_ => c.composed(o.node)).map { x =>
      val complete = if x.discharge == Discharge.Authored then path(l, o.node, "Proofs", "complete")
        else path(l, o.node, "Auto", "complete")
      val holds = Decl.Documented(s"${o.node.value} holds of every world meeting what is below it.",
        Decl.Theorem(Nil, Names.builtin("holds"), Nil, l.props.statement(c.holds(o.node)),
          Proof.Below(c.holdsProof(o.node, complete, x.goal)), Break.SameLine))
      module(l, o.node, NodePart.Theorems, List(holds, audit(l, o.node, NodePart.Theorems, "holds")))
    }

  private def checks(l: Lowering, o: NodeObligations): Option[LeanModule] =
    val others = o.required.filterNot(x => x.name == ObligationName.Complete || x.name == ObligationName.Impl)
    val proven = others.flatMap(x => List(theorem(l, o.node, x), audit(l, o.node, NodePart.Checks,
      LowerObligation.name(x.name).text)))
    val tries = o.tried.map(x => x.discharge match
      case Discharge.Attempt(h) => Decl.Budgeted(h, theorem(l, o.node, x))
      case _                    => theorem(l, o.node, x))
    Option.when(proven.nonEmpty || tries.nonEmpty)(module(l, o.node, NodePart.Checks, proven ++ tries))

  /** `theorem name : Obl.name`, by FrFlow's automation or by the proof file's theorem of that name. */
  private def theorem(l: Lowering, n: NodeId, x: Obligation): Decl =
    val name = LowerObligation.name(x.name)
    val proof = if x.discharge == Discharge.Authored then Proof.Below(path(l, n, "Proofs", name.text))
      else Proof.Tactics(List("frflow_auto"))
    Decl.Theorem(Nil, name, Nil, LExpr.Const(List(Names.builtin("Obl"), name)), proof, Break.SameLine)

  private def audit(l: Lowering, n: NodeId, part: NodePart, name: String): Decl =
    Decl.PrintAxioms(Names.path(l.kb.value, n.value, part.toString, name))

  private def path(l: Lowering, n: NodeId, module: String, name: String): LExpr =
    LExpr.Const(Names.path(l.kb.value, n.value, module, name))

  private val defs: List[Attr] = List(Attr.FrflowDefs)

package frflow
package kb

import frflow.flow.Flows
import frflow.protocol.{NodeKind, tooFew}
import java.util.regex.Pattern.quote

private[frflow] object Validation:
  import Problem.*
  def problems(kb: FrModel): List[Problem] =
    structure(kb) ++ vocabulary(kb) ++ meanings(kb) ++ names(kb) ++ wording(kb) ++ examples(kb) ++ invariants(kb) ++
      code(kb) ++ always(kb) ++ outside(kb) ++ starts(kb)
  private def isOperation(n: Node[?]) = n.kind == NodeKind.Contract || n.kind == NodeKind.Assumption
  /** A claim, a contract or an assumption may leave `why` out: the reason is kept with the decision. */
  private def whyOptional(k: NodeKind) = k == NodeKind.Claim || k == NodeKind.Contract || k == NodeKind.Assumption

  private def structure(kb: FrModel): List[Problem] =
    import kb.{nodes, parentsOf}
    val ids = nodes.map(_.id)
    val called = kb.calledOps
    def under(kind: NodeKind)(n: Node[?]) = parentsOf(n).exists(_.kind == kind)
    List(
      ids.diff(ids.distinct).distinct.map(d => s"duplicate node id $d"),
      // A new project has no nodes while the idea is being written: the roots come first once there are any.
      Option.when(kb.roots.isEmpty && nodes.nonEmpty)(
        "a root is required: a claim with no parents, the idea's purpose (or a contract on the service's flow)").toList,
      // A contract on a flow with parts is made by its code from them: the code must be the proven flow.
      nodes.filter(n => n.isFlow && kb.parts(n).nonEmpty && !kb.implementation(n).exists(_.flow))
        .map(n => s"${n.id} has parts: its flow makes it from them, so implement it with implementProven(${n.id})(flow)"),
      nodes.filter(n => kb.ancestors(n).exists(_ eq n)).map(n => s"${n.id} is above itself: what it is a part of must not lead back to it"),
      nodes.filter(n => isOperation(n) && parentsOf(n).isEmpty && !n.op.exists(o => called(o.name)) &&
          n.modelOf.isEmpty && !n.isAlways &&
          !kb.implementation(n).exists(_.flow))
        .map(n => s"${n.id} has no parents: a ${n.kind.toString.toLowerCase} is a part of the nodes it helps prove, unless code calls its operation"),
      nodes.filter(n => n.kind == NodeKind.Design && n.parents.isEmpty).map(n => s"${n.id}: a design decision is under the nodes it serves (.refines)"),
      nodes.filter(n => n.kind == NodeKind.Definition && n.parents.nonEmpty).map(n => s"${n.id}: a definition has no parents"),
      nodes.flatMap(n => n.parents.filterNot(kb.has).map(p => s"${n.id}: its parent ${p.id} is not in the FrModel")),
      nodes.filter(n => n.kind != NodeKind.Design && under(NodeKind.Design)(n))
        .map(n => s"${n.id}: a design decision has no statement to refine; only design decisions go below it"),
      nodes.filter(under(NodeKind.Definition)).map(n => s"${n.id}: nothing is under a definition; a node uses its terms")
    ).flatten.map(Structure(_))

  private def vocabulary(kb: FrModel): List[Problem] =
    import kb.{definitions, nodes}
    List(
      definitions.filter(n => n.substs.isEmpty).map(n => s"${n.id}: a definition fixes at least one term"),
      definitions.flatMap(d => d.defines.diff(d.defines.distinct).distinct.map(t => s"${d.id} defines $t twice")),
      definitions.filter(d => kb.definitionsUsed(d, kb.provisional).exists(_ eq d)).map(d => s"${d.id}: its terms are defined through themselves"),
      definitions.flatMap(d => d.defines.filter(kb.isOp).map(t => s"${d.id} defines $t, an operation: code implements an operation, a definition does not")),
      // Something exists of a type holding an Int or Long: Lean's integers are unbounded, so it may not in Scala.
      definitions.flatMap { d =>
        d.substs.filter(s => s.isType && s.types.exists(t => """:\s*(Int|Long)\b""".r.findFirstIn(t.scala).isDefined)).flatMap { s =>
          val ex = s"∃ \\([^)]*: ${quote(s.name)}\\)".r
          nodes.flatMap(_.referenced).find(l => ex.findFirstIn(l.body).isDefined).map(_ =>
            s"${d.id}: ${s.name} := ${s.lean}, whose values hold an Int or Long, but something says one exists: Lean's integers are unbounded, Scala's are not; use BigInt")
        }
      }
    ).flatten.map(Vocabulary(_))

  /** A Definition gets a meaning from code; a Declaration never does, and no code uses it. */
  private def meanings(kb: FrModel): List[Problem] =
    val declarations = kb.params.collect { case d: Declaration[?] => d.name }.toSet
    val usedByCode = kb.implementations.flatMap(i =>
      i.proven.toList.flatMap(d => Def.closure(List(d)).flatMap(_.lifted.paramObjects)).map(_.name) ++ i.calls).distinct
    List(
      kb.params.collect { case d: Definition[?] if !kb.defines(d) => d.name }
        .map(d => s"$d is a Definition nothing defines: give it its meaning with implementProven($d)(…) or " +
          s"implementTested($d)(…)"),
      kb.implementations.flatMap(i => kb.node(i.contract).flatMap(_.op)).map(_.name).filter(declarations).distinct
        .map(d => s"$d is a Declaration, known only by what is said of it: it is never implemented " +
          "(make it a Definition to give it code)"),
      usedByCode.filter(declarations)
        .map(d => s"code uses $d, a Declaration: code uses only Definitions, and a Declaration is known only by " +
          "what is said of it"),
      kb.params.collect { case d: Definition[?] if kb.defines(d) && kb.claimsOn(d).isEmpty => d.name }
        .map(d => s"$d: no claim says what it does, so nothing checks its code: state one " +
          s"(Node.claim(…)(forall(… $d(…) …)))")
    ).flatten.map(Vocabulary(_))

  /** What an `always` claim about a store rests on: the store's start, who writes it, and one run at a time. */
  private def always(kb: FrModel): List[Problem] =
    val proven = kb.implementations.filter(_.flow)
      .flatMap(i => i.definition.orElse(kb.node(i.contract).flatMap(_.op).map(_.name)))
    kb.nodes.flatMap(n => n.always.flatMap(_.store).map(n -> _)).flatMap { (n, m) =>
      val facts = kb.premisesOf(n).flatMap(_.fact).filter(_.store.exists(_ eq m)).map(_.says)
      val writers = facts.collect { case FactKind.WrittenOnlyBy(ps) => ps.map(_.name) }.flatten
      List(
        Option.when(!facts.exists(f => f.isInstanceOf[FactKind.Initially]) &&
            !kb.premisesOf(n).exists(_.startsSatisfying.exists(_ eq n)))(
          s"${n.id}: say what the store holds when the system starts, an assumption it rests on: " +
          s".assuming(Node.assumption(\"…\")(${m.lean}.startsSatisfying(${n.id.head.toLower}${n.id.tail}))), or " +
          s"${m.lean}.initially(…)"),
        Option.when(!facts.exists(_.isInstanceOf[FactKind.WrittenOnlyBy]))(s"${n.id}: say which programs change the " +
          s"store, an assumption it rests on: .assuming(Node.assumption(\"…\")(${m.lean}.writtenOnlyBy(…)))"),
        Option.when(!facts.contains(FactKind.OneRunAtATime))(s"${n.id}: say that one run changes the store at a " +
          "time, " +
          s"an assumption it rests on: .assuming(Node.assumption(\"…\")(${m.lean}.changedOneRunAtATime))")
      ).flatten ++ writers.filterNot(proven.contains)
        .map(w => s"${n.id}: $w changes the store, so it keeps ${n.id}: give it proven code (implementProven($w)(…))")
    }.map(Invariants(_))

  /** What comes from outside (the inputs of the programs with proven code) is not made by covered code: what it
    * meets is an assumption `always` of its type. An `always` claim about a type such values have, with no such
    * assumption, has nothing to rest on there.
    */
  private def outside(kb: FrModel): List[Problem] =
    val programs = kb.implementations.filter(_.flow).flatMap(i => kb.node(i.contract).flatMap(_.op)).distinctBy(_.name)
    def inputs(p: Param[?]) = p.termType.shape match
      case frflow.types.Shape.FnOf(as, _) => as
      case _                              => Nil
    def ruleType(n: Node[?]) = n.holds.map(_.lifted.built._1.head.tpe)
    val assumed = kb.nodes.filter(a => a.kind == NodeKind.Assumption && a.always.exists(_.store.isEmpty))
      .flatMap(ruleType).map(Types.walk(_).lean).toSet
    (for
      p <- programs
      t <- inputs(p)
      (n, _, _) <- kb.invariantsOn(t)
      rt <- ruleType(n) if n.kind == NodeKind.Claim && !assumed(Types.walk(rt).lean)
    yield (n, p, rt)).distinctBy((n, p, _) => (n.id, p.name)).map { (n, p, rt) =>
      val v = Types.scala(rt)
      Invariants(s"${n.id}: ${p.name} is given values of $v from outside, which no covered code makes: say what " +
        s"the outside sends, Node.assumption(\"…\")(always[$v](x => …)), on a type of its own if covered code " +
        s"also makes $v")
    }

  /** What a store starts satisfying is an `always` claim about that store. */
  private def starts(kb: FrModel): List[Problem] =
    kb.nodes.flatMap(n => n.fact.flatMap(_.store).toList.flatMap(m => n.startsSatisfying.map(c => (n, m, c))))
      .filterNot((_, m, c) => c.always.exists(_.store.exists(_ eq m)))
      .map((n, m, c) => Invariants(s"${n.id}: ${c.id} is not an always claim about " +
        s"${m.lean}: say what the store starts satisfying with always(${m.lean})(…)"))

  private def names(kb: FrModel): List[Problem] =
    val ids = kb.nodes.map(_.id)
    val Ident = """[A-Za-z_][A-Za-z0-9_]*""".r
    val declared = kb.types.map(_.name) ++ kb.defs.map(_.name)
    val terms = kb.params.map(_.name) ++ kb.opaques.map(_.name)
    def twice[A](xs: List[A], name: A => String)(say: (String, List[A]) => String): List[String] =
      xs.distinct.groupBy(name).collect { case (n, as) if as.size > 1 => say(n, as) }.toList
    List(
      ids.filterNot(Ident.matches).map(i => s"node id $i is not an identifier"),
      ids.filter(i => i == "Lemmas" || i == "RootImpl").map(i => s"node id $i is reserved in lean/"),
      ids.filter(_ == "IDEA").map(_ => "node id IDEA is reserved: the ledger keeps the decision on IDEA.md under it"),
      // Lean would prove one while Scala runs the other.
      twice(kb.allDefs, _.name)((n, _) => s"two different definitions are named $n (in different packages, say): Lean would know only one of them; rename one"),
      twice(kb.paramObjects, _.name)((p, ps) => s"two different parameters are named $p: ${ps.map(_.means).mkString("; ")}; rename one").sorted,
      twice(kb.lifteds.flatMap(_.opaqueObjects), _.name)((o, _) => s"two different opaque types are named $o; rename one").sorted,
      kb.opaques.map(_.name).filterNot((kb.lifteds.flatMap(_.opaques) ++ kb.definitions.flatMap(_.defines)).contains)
        .map(n => s"opaque type $n: the val name and the name given to Opaque differ"),
      ids.filter(i => declared.contains(i) || terms.contains(i)).map(i => s"node id $i clashes with a type, function or term of the same name"),
      terms.filter(declared.contains).distinct.map(n => s"term $n clashes with a type or function of the same name"),
      kb.nodes.flatMap(_.referenced).flatMap(_.paramRefs).map(_._1).distinct.filterNot(n => kb.params.exists(_.name == n))
        .map(n => s"parameter $n: the val name and the name given to Param differ"),
      kb.lifteds.flatMap(_.types).groupBy(_.name).collect {
        case (n, ds) if ds.map(_.body).distinct.size > 1 => s"two different Scala types are named $n"
      }.toList
    ).flatten.map(Vocabulary(_))

  private def wording(kb: FrModel): List[Problem] =
    List(
      kb.nodes.filter(n => n.why.trim.isEmpty && !whyOptional(n.kind))
        .map(n => s"${n.id}: say why (the reason for this node)"),
      (kb.params.filter(_.means.trim.isEmpty).map(_.name) ++ kb.opaques.filter(_.means.trim.isEmpty).map(_.name))
        .map(n => s"$n: say what it means in the world"),
      kb.nodes.filter(_.statement.trim.isEmpty).map(n => s"${n.id}: empty statement")
    ).flatten.map(Wording(_))

  /** Examples are cases the developer reads, not what anything rests on: only where there is a call to give them of. */
  private def examples(kb: FrModel): List[Problem] =
    kb.nodes.filter(n => n.cases.nonEmpty && n.post.isEmpty)
      .map(n => Examples(s"${n.id}: only contracts and assumptions on an operation have examples"))

  private def invariants(kb: FrModel): List[Problem] =
    import kb.nodes
    val rules = nodes.filter(_.isInvariant)
    def keeps(n: Node[?], i: Node[?]) = n.kept.exists(k => (k.invariant eq i) && k.view.nonEmpty)
    List(
      nodes.flatMap(n => n.kept.map(_.invariant).filterNot(i => kb.has(i) && i.isInvariant)
        .map(i => s"${n.id} keeps ${i.id}, which is not an invariant of this FrModel")),
      nodes.filter(n => n.kept.exists(_.view.nonEmpty) && !n.onOperation)
        .map(n => s"${n.id}: only contracts keep invariants"),
      nodes.filter(n => n.kept.nonEmpty && !n.onOperation && n.kind != NodeKind.Design)
        .map(n => s"${n.id}: only contracts and design decisions are exempt from invariants"),
      nodes.flatMap(n => n.kept.groupBy(_.invariant.id).collect { case (i, ks) if ks.size > 1 => s"${n.id} names $i more than once" }),
      nodes.flatMap(n => n.kept.filter(k => k.view.isEmpty && tooFew(k.exempt))
        .map(k => s"${n.id}: say in a few words why ${k.invariant.id} does not apply to it")),
      rules.flatMap(i => kb.inScope(i).filterNot(_.kept.exists(_.invariant eq i))
        .map(c => if c.kind == NodeKind.Design then s"${c.id}: say why ${i.id} does not apply to the code it governs (.exempt): a design decision in its scope does"
          else s"${c.id}: keep ${i.id} (.keeps) or say why it does not apply (.exempt): every contract in its scope does one")),
      rules.filterNot(i => nodes.exists(keeps(_, i))).map(i => s"${i.id}: no contract keeps this invariant"),
      rules.flatMap(i => i.scope.filterNot(kb.has).map(s => s"${i.id}: its scope ${s.id} is not in the FrModel"))
    ).flatten.map(Invariants(_))

  private def code(kb: FrModel): List[Problem] =
    val boundaries = kb.implementations.flatMap(_.flowDef).flatMap(_.lifted.boundaries).distinct
    List(
      boundaries.filterNot(b => kb.models.exists(_.boundary eq b))
        .map(b => s"the boundary ${b.name}: proven flows call it, so decide what it does (Node.assumption(${b.name})(SomeModel)(…))"),
      kb.models.groupBy(_.boundary).collect { case (b, ms) if ms.size > 1 => s"the boundary ${b.name} has ${ms.size} models: decide one" }.toList,
      kb.models.filterNot(m => m.boundary.cls.isInstance(m.model)).map(m => s"${m.model.lean} is not an implementation of ${m.boundary.cls.getSimpleName}"),
      kb.implementations.flatMap(_.flowDef).filter(d => d.lifted.built._2.termTree match { case Tree.Do(s) => Steps.effectful(s); case _ => false })
        .map(d => s"${d.name}: a proven flow takes no step of the outside world (Flow.effect): call a boundary"),
      // A flow that may fail is attached to a contract that says what holds when it does, with the error's type.
      kb.implementations.flatMap(i => i.flowDef.map(i.contract -> _)).flatMap { (c, d) =>
        val errs = d.lifted.built._2.termTree match { case Tree.Do(s) => Flows.errorTypes(s); case _ => Nil }
        val said = kb.nodes.find(_.id == c).flatMap(_.failure).map(f => Types.walk(f.err).lean)
        errs.map(e => Types.walk(e).lean).distinct match
          case Nil => Nil
          case List(e) if said.forall(_ == e) =>
            Option.when(said.isEmpty)(s"$c: its flow may fail with $e: say what holds when a run fails (.failsChangingNothing[…] or .onFailure[…](…))").toList
          case es => List(s"$c: its flow may fail with ${es.mkString(" or ")}${said.fold("")(s => s", its contract says $s")}: one error type for a flow")
      },
      kb.failureTypes.drop(1).headOption.map(_ => s"the flows fail with ${kb.failureTypes.mkString(" and ")}: one error type for a FrModel").toList,
      // Code that calls its own operation would be proven assuming what it proves.
      kb.nodes.flatMap(c => c.op.filter(o => kb.implementation(c).flatMap(_.proven).exists(d => kb.opsCalledBy(d).contains(o.name)))
        .map(o => s"${c.id}: its implementation calls ${o.name} itself: it cannot be proven from its own promise")),
      kb.implementations.map(_.contract).filterNot(c => kb.nodes.exists(n => n.id == c && n.op.isDefined))
        .map(c => s"implementation of $c: not a contract (or an assumption on an operation) of this FrModel"),
      kb.nodes.filter(n => n.runCheck.isDefined && kb.runTime(n).isEmpty)
        .map(n => s"${n.id}: checkedAtRunTime is for a contract or an assumption whose code service runs: attach its code, or remove it")
    ).flatten.map(Code(_))

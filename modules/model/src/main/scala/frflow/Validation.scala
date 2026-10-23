package frflow

import java.util.regex.Pattern.quote

/** What keeps a knowledge base from being checked: one thing wrong with it, said so that its author
  * can fix it. The case says what part of the model it is about.
  */
enum Problem(val message: String):
  /** The DAG: the root, parents, cycles, what may go under what. */
  case Structure(text: String) extends Problem(text)
  /** The vocabulary: definitions, terms, types, and names that clash or differ. */
  case Vocabulary(text: String) extends Problem(text)
  /** What the developer reads: a statement, a why, what a term means. */
  case Wording(text: String) extends Problem(text)
  /** The examples a contract needs. */
  case Examples(text: String) extends Problem(text)
  /** Invariants: who keeps them, who is exempt, and why. */
  case Invariants(text: String) extends Problem(text)
  /** Code attached to contracts. */
  case Code(text: String) extends Problem(text)

  override def toString: String = message

/** The structural checks of a knowledge base (`KnowledgeBase.problems`). */
private[frflow] object Validation:
  import Problem.*

  def problems(kb: KnowledgeBase): List[Problem] =
    structure(kb) ++ vocabulary(kb) ++ names(kb) ++ wording(kb) ++ examples(kb) ++ invariants(kb) ++ code(kb)

  private def isOperation(n: Node[?]) = n.kind == NodeKind.Contract || n.kind == NodeKind.Assumption

  private def structure(kb: KnowledgeBase): List[Problem] =
    import kb.{nodes, parentsOf}
    val ids = nodes.map(_.id)
    // The operations some code calls (plain code calls one through its parameter: `decide.value(...)`, `decide(...)`).
    val called = kb.implementations.flatMap(_.proven).flatMap(kb.opsCalledBy).toSet ++
      kb.onOp.keySet.filter(o => kb.implementations.exists(i => s"\\b${quote(o)}\\b".r.findFirstIn(i.wiring).isDefined))
    def under(kind: NodeKind)(n: Node[?]) = parentsOf(n).exists(_.kind == kind)
    List(
      ids.diff(ids.distinct).distinct.map(d => s"duplicate node id $d"),
      kb.roots match
        case List(_) => Nil
        case Nil     => List("a root is required: one claim with no parents, the idea's purpose")
        case rs      => List(s"one root only: ${rs.map(_.id).mkString(", ")} are claims with no parents; put all but one under the nodes they help prove"),
      // What a node rests on (its parents) must not lead back to it.
      nodes.filter(n => kb.ancestors(n).exists(_ eq n)).map(n => s"${n.id} is above itself: what it is a part of must not lead back to it"),
      nodes.filter(n => isOperation(n) && n.parents.isEmpty && !n.op.exists(o => called(o.name)))
        .map(n => s"${n.id} has no parents: a ${n.kind.toString.toLowerCase} is a part of the nodes it helps prove, unless code calls its operation"),
      nodes.filter(n => n.kind == NodeKind.Design && n.parents.isEmpty).map(n => s"${n.id}: a design decision is under the nodes it serves (.under)"),
      nodes.filter(n => n.kind == NodeKind.Definition && n.parents.nonEmpty).map(n => s"${n.id}: a definition has no parents"),
      nodes.flatMap(n => n.parents.filterNot(kb.has).map(p => s"${n.id}: its parent ${p.id} is not in the knowledge base")),
      nodes.filter(n => n.kind != NodeKind.Design && under(NodeKind.Design)(n))
        .map(n => s"${n.id}: a design decision has no statement to refine; only design decisions go below it"),
      nodes.filter(under(NodeKind.Definition)).map(n => s"${n.id}: nothing is under a definition; a node uses its terms")
    ).flatten.map(Structure(_))

  private def vocabulary(kb: KnowledgeBase): List[Problem] =
    import kb.{definitions, nodes}
    List(
      definitions.filter(_.substs.isEmpty).map(n => s"${n.id}: a definition fixes at least one term"),
      definitions.flatMap(d => d.defines.diff(d.defines.distinct).distinct.map(t => s"${d.id} defines $t twice")),
      // A term defined through itself has no meaning.
      definitions.filter(d => kb.definitionsUsed(d, kb.provisional).exists(_ eq d)).map(d => s"${d.id}: its terms are defined through themselves"),
      definitions.flatMap(d => d.defines.filter(kb.isOp).map(t => s"${d.id} defines $t, an operation: code implements an operation, a definition does not")),
      // An opaque type something says exists of, fixed to a type that holds an Int or Long: Lean's
      // integers are unbounded, so what Lean finds may not exist in Scala.
      definitions.flatMap { d =>
        d.substs.filter(s => s.isType && s.types.exists(t => """:\s*(Int|Long)\b""".r.findFirstIn(t.scala).isDefined)).flatMap { s =>
          val ex = s"∃ \\([^)]*: ${quote(s.name)}\\)".r
          nodes.flatMap(_.lifted).find(l => ex.findFirstIn(l.body).isDefined).map(_ =>
            s"${d.id}: ${s.name} := ${s.lean}, whose values hold an Int or Long, but something says one exists: Lean's integers are unbounded, Scala's are not; use BigInt")
        }
      }
    ).flatten.map(Vocabulary(_))

  /** Names: what Lean and the run time tell apart only by name must have one name each. */
  private def names(kb: KnowledgeBase): List[Problem] =
    val ids = kb.nodes.map(_.id)
    val Ident = """[A-Za-z_][A-Za-z0-9_]*""".r
    val declared = kb.types.map(_.name) ++ kb.defs.map(_.name)
    val terms = kb.params.map(_.name) ++ kb.opaques.map(_.name)
    def twice[A](xs: List[A], name: A => String)(say: (String, List[A]) => String): List[String] =
      xs.distinct.groupBy(name).collect { case (n, as) if as.size > 1 => say(n, as) }.toList
    List(
      ids.filterNot(Ident.matches).map(i => s"node id $i is not an identifier"),
      ids.filter(i => i == "Lemmas" || i == "RootImpl").map(i => s"node id $i is reserved in lean/"),
      // Two definitions by one name (in two packages, say) would be one in Lean: Lean would prove one
      // while Scala runs the other.
      twice(kb.allDefs, _.name)((n, _) => s"two different definitions are named $n (in different packages, say): Lean would know only one of them; rename one"),
      // Two different parameters (or opaque types) with one name would be one in Lean and at run time.
      twice(kb.paramObjects, _.name)((p, ps) => s"two different parameters are named $p: ${ps.map(_.means).mkString("; ")}; rename one").sorted,
      twice(kb.lifteds.flatMap(_.opaqueObjects), _.name)((o, _) => s"two different opaque types are named $o; rename one").sorted,
      kb.opaques.map(_.name).filterNot((kb.formalLifteds.flatMap(_.opaques) ++ kb.definitions.flatMap(_.defines)).contains)
        .map(n => s"opaque type $n: the val name and the name given to Opaque differ"),
      ids.filter(i => declared.contains(i) || terms.contains(i)).map(i => s"node id $i clashes with a type, function or term of the same name"),
      terms.filter(declared.contains).distinct.map(n => s"term $n clashes with a type or function of the same name"),
      kb.nodes.flatMap(_.lifted).flatMap(_.paramRefs).map(_._1).distinct.filterNot(n => kb.params.exists(_.name == n))
        .map(n => s"parameter $n: the val name and the name given to Param differ"),
      kb.formalLifteds.flatMap(_.types).groupBy(_.name).collect {
        case (n, ds) if ds.map(_.body).distinct.size > 1 => s"two different Scala types are named $n"
      }.toList
    ).flatten.map(Vocabulary(_))

  private def wording(kb: KnowledgeBase): List[Problem] =
    List(
      kb.nodes.filter(_.why.trim.isEmpty).map(n => s"${n.id}: say why (the reason for this node)"),
      (kb.params.filter(_.means.trim.isEmpty).map(_.name) ++ kb.opaques.filter(_.means.trim.isEmpty).map(_.name))
        .map(n => s"$n: say what it means in the world"),
      kb.nodes.filter(_.statement.trim.isEmpty).map(n => s"${n.id}: empty statement")
    ).flatten.map(Wording(_))

  private def examples(kb: KnowledgeBase): List[Problem] =
    val contracts = kb.nodes.filter(_.kind == NodeKind.Contract)
    List(
      kb.nodes.filter(n => n.cases.nonEmpty && n.post.isEmpty).map(n => s"${n.id}: only contracts and assumptions on an operation have examples"),
      contracts.filterNot(n => n.cases.exists(_.expected) && n.cases.exists(!_.expected))
        .map(n => s"${n.id}: a contract needs examples: at least one expect (what it must allow) and one reject"),
      // An implementation that always returns the same value must fail some example.
      contracts.flatMap { n =>
        n.cases.filter(_.expected).map(_.result).distinct match
          case List(v) if !n.cases.exists(e => !e.expected && e.result == v) =>
            List(s"${n.id}: every expect returns ${Example.show(v)}, so an implementation that always returns it would pass the examples; add an expect with another result")
          case _ => Nil
      }
    ).flatten.map(Examples(_))

  private def invariants(kb: KnowledgeBase): List[Problem] =
    import kb.nodes
    val rules = nodes.filter(_.isInvariant)
    def keeps(n: Node[?], i: Node[?]) = n.kept.exists(k => (k.invariant eq i) && k.view.nonEmpty)
    List(
      nodes.flatMap(n => n.kept.map(_.invariant).filterNot(i => kb.has(i) && i.isInvariant)
        .map(i => s"${n.id} keeps ${i.id}, which is not an invariant of this knowledge base")),
      nodes.filter(n => n.kept.exists(_.view.nonEmpty) && n.kind != NodeKind.Contract).map(n => s"${n.id}: only contracts keep invariants"),
      nodes.filter(n => n.kept.nonEmpty && n.kind != NodeKind.Contract && n.kind != NodeKind.Design)
        .map(n => s"${n.id}: only contracts and design decisions are exempt from invariants"),
      nodes.flatMap(n => n.kept.groupBy(_.invariant.id).collect { case (i, ks) if ks.size > 1 => s"${n.id} names $i more than once" }),
      nodes.flatMap(n => n.kept.filter(k => k.view.isEmpty && Words.tooFew(k.exempt))
        .map(k => s"${n.id}: say in a few words why ${k.invariant.id} does not apply to it")),
      rules.flatMap(i => kb.inScope(i).filterNot(_.kept.exists(_.invariant eq i))
        .map(c => if c.kind == NodeKind.Design then s"${c.id}: say why ${i.id} does not apply to the code it governs (.exempt): a design decision in its scope does"
          else s"${c.id}: keep ${i.id} (.keeps) or say why it does not apply (.exempt): every contract in its scope does one")),
      rules.filterNot(i => nodes.exists(keeps(_, i))).map(i => s"${i.id}: no contract keeps this invariant"),
      rules.flatMap(i => i.scope.filterNot(kb.has).map(s => s"${i.id}: its scope ${s.id} is not in the knowledge base"))
    ).flatten.map(Invariants(_))

  private def code(kb: KnowledgeBase): List[Problem] =
    List(
      // Code that calls its own operation would be proven assuming what it proves.
      kb.nodes.flatMap(c => c.op.filter(o => kb.implementation(c).flatMap(_.proven).exists(d => kb.opsCalledBy(d).contains(o.name)))
        .map(o => s"${c.id}: its implementation calls ${o.name} itself: it cannot be proven from its own promise")),
      kb.implementations.map(_.contract).filterNot(c => kb.nodes.exists(n => n.id == c && n.op.isDefined))
        .map(c => s"implementation of $c: not a contract (or an assumption on an operation) of this knowledge base")
    ).flatten.map(Code(_))

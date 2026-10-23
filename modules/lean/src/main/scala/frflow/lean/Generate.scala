package frflow
package lean

import frflow.protocol.ObligationName

/** The Lean of a knowledge base (docs/DAG.md §3; where each module lives: `Layout`), put together from
  * its parts: the terms (`Vocabulary`), how the nodes refine each other (`Refinement`), what Lean is
  * asked of each (`Obligations`, `Coverage`), the examples evaluated (`Evals`), and the text of each
  * module (`VocabularyModules`, `NodeModules`, `ProofFiles`).
  *
  * @param authored (node, obligation) proven by a theorem of that name in `Proofs/<KB>/<Node>.lean`
  * @param chosen   the definitions decided among alternatives (two definitions of one term)
  */
final class Generate(kb: KnowledgeBase, authored: Set[(String, ObligationName)] = Set.empty, chosen: String => Boolean = _ => false):
  val layout: Layout = Layout(kb.name)
  val vocabulary: Vocabulary = Vocabulary(kb, chosen)
  val refinement: Refinement = Refinement(kb, vocabulary)
  private val coverages = Coverage(kb, refinement)
  private val asked = Obligations(kb, refinement, coverages, authored)
  private val evaluated = Evals(kb, refinement, LeanValues(kb))
  private val vocabularyModules = VocabularyModules(kb, layout, vocabulary)
  private val nodeModules = NodeModules(kb, layout, refinement, vocabularyModules, asked, evaluated)
  private val proofFiles = ProofFiles(kb, layout, refinement)

  export vocabulary.{inForce, undecided, term, waitsForDefinition}
  export refinement.{formal, splitParts, formalKeeps, provenImpl, claim, callees, calls, leaves, holdsStatement, trusted, witnessed}
  export coverages.coverage
  export asked.{isAuthored, obligations, obligation, extraObligations, tries, idle, idleWhat}
  export evaluated.evals
  export vocabularyModules.{types, domainModule, domain}
  export nodeModules.{spec, auto, impl, theorems, checks, evalFile, rootImpl}
  export proofFiles.{stubs, proofFile, goalFile, lakefile}

  /** Every generated file, by its path in the Lean workspace. */
  def files: Map[String, String] =
    val perNode = kb.nodes.filter(formal).flatMap { n =>
      List(layout.spec(n.id) -> spec(n), layout.auto(n.id) -> auto(n), layout.theorems(n.id) -> theorems(n), layout.checks(n.id) -> checks(n)) ++
        provenImpl(n).map(_ => layout.impl(n.id) -> impl(n)) ++ evalFile(n).map(layout.eval(n.id) -> _)
    }
    val modules = List(layout.domain -> domainModule, layout.types -> types) ++ rootImpl.map(r => layout.rootImpl -> r._2) ++ perNode
    (modules.map((m, text) => m.path -> text) ++ vocabularyModules.files).toMap

  /** Lean of the domain types, functions and definitions a node's own expressions use. */
  def declarationsUsedBy(n: Node[?]): List[String] =
    val rules = formalKeeps(n).flatMap(_._1.rule)
    val defs = Def.closure((n.referenced ++ rules).flatMap(_.defs) ++ provenImpl(n))
    val ls = n.referenced ++ rules ++ defs.map(_.lifted)
    ls.flatMap(_.types).map(_.body).distinct ++ defs.map(d => vocabulary.resolve(d.lifted.lean)) ++
      kb.definitionsUsed(n, inForce).flatMap(_.substs).map(s => s"${s.name} := ${s.lean}")

  /** What a node uses, as written in Scala: the domain types and the `define`s, however nested. Part of
    * what a decision is bound to; unlike the generated Lean, it does not change when FrFlow's translation does.
    */
  def sourcesUsedBy(n: Node[?]): List[String] =
    val defs = Def.closure(n.referenced.flatMap(_.defs))
    val types = (n.referenced ++ defs.map(_.lifted)).flatMap(_.types) ++ n.substs.flatMap(_.types)
    types.map(t => if t.scala.nonEmpty then t.scala else t.lean).distinct ++ defs.map(d => s"${d.name} = ${d.lifted.source}")

object Generate:
  /** Names the generated Lean binds itself; a parameter or opaque type with one of them would be captured. */
  val reserved: Set[String] =
    Names.Prelude ++ Set("m", "f", "h", "p", "claim", "post", "rule", "holds", "complete", "impl", "Obl", "Type", "Prop") ++ (0 to 9).map(i => s"x$i")

  /** How many probes of a contract Lean evaluates, beside its examples. */
  val ProbeCount = 6

  /** The work a try (a statement Lean is asked whether it can prove) may take: a try is one-sided and cheap.
    * A try that fails says only that Lean found no proof within it. The root's `idle` (one per knowledge
    * base) runs at Lean's default budget: at this one it gives up on a root of the CRM's size.
    */
  val TryHeartbeats = 4000

  /** What generated Lean cannot hold: a parameter or opaque type with a name it binds itself. */
  def problems(kb: KnowledgeBase): List[String] =
    (kb.params.map(_.name) ++ kb.opaques.map(_.name)).distinct.filter(reserved)
      .map(n => s"parameter or opaque type $n: the name is reserved in generated Lean")

package frflow
package lean

import frflow.protocol.ObligationName

/** The Lean of a FrModel (docs/DAG.md §3), put together from its parts. `authored` are the
  * (node, obligation) its proof files prove; `chosen`, the definitions decided among alternatives.
  */
final class Generate(kb: FrModel, authored: Set[(String, ObligationName)] = Set.empty, chosen: String => Boolean = _ => false):
  val layout: Layout = Layout(kb.name)
  val vocabulary: Vocabulary = Vocabulary(kb, chosen)
  val refinement: Refinement = Refinement(kb, vocabulary)
  private val coverages = Coverage(kb, refinement)
  private val asked = Obligations(kb, refinement, coverages, authored)
  private val evaluated = Evals(kb, refinement)
  private val vocabularyModules = VocabularyModules(kb, layout, vocabulary)
  val boundaryModules: BoundaryModules = BoundaryModules(kb, layout, vocabulary, vocabularyModules)
  private val nodeModules = NodeModules(kb, layout, refinement, vocabularyModules, asked, evaluated)
  private val proofFiles = ProofFiles(kb, layout, refinement)
  /** What the FrModel as a whole is asked (docs/DAG.md §3a). */
  val witnessing: Witnessing = Witnessing(kb, refinement, layout, vocabularyModules)
  export vocabulary.{inForce, undecided, term, waitsForDefinition}
  export refinement.{formal, splitParts, formalKeeps, provenImpl, claim, callees, reliedOn, calls, leaves, holdsStatement, trusted, witnessed}
  export coverages.coverage
  export asked.{isAuthored, obligations, obligation, extraObligations, tries, idle, idleWhat}
  export evaluated.evals
  export vocabularyModules.{types, domainModule, domain}
  export nodeModules.{spec, auto, impl, theorems, checks, evalFile, rootImpl}
  export proofFiles.{stubs, proofFile, goalFile, lakefile}

  def files: Map[String, String] =
    val perNode = kb.nodes.filter(formal).flatMap { n =>
      List(layout.spec(n.id) -> spec(n), layout.auto(n.id) -> auto(n), layout.theorems(n.id) -> theorems(n), layout.checks(n.id) -> checks(n)) ++
        provenImpl(n).map(_ => layout.impl(n.id) -> impl(n)) ++ evalFile(n).map(layout.eval(n.id) -> _)
    }
    val modules = List(layout.domain -> domainModule, layout.types -> types) ++
      kb.roots.flatMap(r => rootImpl(r).map(x => layout.rootImpl(r.id) -> x._2)) ++
      Option.when(boundaryModules.exist)(layout.boundaries -> boundaryModules.file) ++
      Option.when(witnessing.asked.nonEmpty)(layout.consistency -> witnessing.file) ++ perNode
    (modules.map((m, text) => m.path -> text) ++ vocabularyModules.files).toMap

  def declarationsUsedBy(n: Node[?]): List[String] =
    val rules = formalKeeps(n).flatMap(_._1.rule)
    val defs =
      Def.closure((n.referenced ++ rules).flatMap(_.defs) ++ provenImpl(n) ++ kb.invariantsUsedBy(n).flatMap(_.holds))
    val ls = n.referenced ++ rules ++ defs.map(_.lifted)
    ls.flatMap(_.types).map(_.body).distinct ++ defs.map(d => vocabulary.resolve(d.lifted.lean)) ++
      kb.definitionsUsed(n, inForce).flatMap(_.substs).map(s => s"${s.name} := ${s.lean}")

  /** What a node uses, as written in Scala: decisions bind it, and it does not move when FrFlow's translation does. */
  def sourcesUsedBy(n: Node[?]): List[String] =
    val defs = Def.closure(n.referenced.flatMap(_.defs))
    val types = (n.referenced ++ defs.map(_.lifted)).flatMap(_.types) ++ n.substs.flatMap(_.types)
    types.map(t => if t.scala.nonEmpty then t.scala else t.lean).distinct ++ defs.map(d => s"${d.name} = ${d.lifted.source}")

object Generate:
  /** Names the generated Lean binds itself; a parameter or opaque type with one of them would be captured. */
  val reserved: Set[String] =
    Names.Prelude ++ Set("m", "f", "h", "p", "claim", "post", "rule", "holds", "complete", "impl", "Obl", "Type", "Prop") ++ (0 to 9).map(i => s"x$i")
  val ProbeCount = 6

  /** A try is one-sided and cheap; the root's `idle` runs at Lean's default: at this it gives up on the CRM's root. */
  val TryHeartbeats = 4000

  def problems(kb: FrModel): List[String] =
    (kb.params.map(_.name) ++ kb.opaques.map(_.name)).distinct.filter(reserved)
      .map(n => s"parameter or opaque type $n: the name is reserved in generated Lean")

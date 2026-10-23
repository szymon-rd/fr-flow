package frflow
package lean

import scala.collection.immutable.ListSet
import LeanText.*

/** The vocabulary in Lean: the domain types (`Types`), each `define` (over the terms it mentions) and each
  * term a definition in force fixes (a `def` over the terms its definition mentions) in a module of its
  * own, importing the `define`s it calls; `Domain` imports them all. A node's model imports only what it
  * uses (`modulesFor`): a change to one `define` (code, say) or one definition rebuilds the nodes that use
  * it, not every node of the knowledge base.
  */
final class VocabularyModules(kb: KnowledgeBase, layout: Layout, vocabulary: Vocabulary):
  import vocabulary.*
  private val K = kb.name

  def types: String =
    val abbrevs = definitionsInForce.collect { case (t, d, s) if s.isType => s"/-- ${d.id} -/\n@[frflow_defs] abbrev $t : Type := ${s.lean}" }
    module(List(LeanModule("FrFlow")), K, (kb.types.map(_.lean) ++ abbrevs).mkString("\n\n") + "\n\n")

  /** A module of the vocabulary: one declaration, with the equations of its matches (see `MatchEqns`). */
  private def declaring(uses: List[LeanModule], decl: String): String =
    module((layout.types :: uses).distinct, K, decl + "\n\n" + MatchEqns + "\n")

  /** The terms defined by an expression, as definitions (no types): each term with its expression. */
  private def definedTerms: List[(String, Node[?], Lifted[?])] =
    definitionsInForce.collect { case (t, d, s) if !s.isType => s.term.map((t, d, _)) }.flatten

  /** The modules of the vocabulary, by path. */
  def files: List[(String, String)] =
    val defs = kb.defs.map { d =>
      layout.definition(d.name).path -> declaring(d.lifted.defs.map(_.name).filter(x => x != d.name && defNames(x)).map(layout.definition),
        definition(d.name, binders(defCtx(d)), d.lifted.leanType, resolve(d.lifted.lean)))
    }
    val terms = definedTerms.map { (t, d, l) =>
      layout.term(t).path -> declaring(l.defs.map(_.name).filter(defNames).map(layout.definition),
        s"/-- ${d.id} -/\n" + definition(t, binders(ctx(l)), l.leanType, resolve(l.lean)))
    }
    defs ++ terms

  /** The whole vocabulary, in one module that imports every part of it: what proof files and lemmas import. */
  def domainModule: String =
    Header + imports((layout.types :: kb.defs.map(d => layout.definition(d.name)) ++ definedTerms.map(t => layout.term(t._1))).distinct)

  /** The vocabulary's declarations, together (to read; the modules above hold them). */
  def domain: String = (types :: files.map(_._2)).mkString("\n")

  /** The `define`s and terms in force some declarations need, in the order they are met. */
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

  /** The vocabulary modules some declarations need: the `define`s they call, however nested, and the
    * terms in force they mention, with what those terms' definitions need in turn.
    */
  def modulesFor(defs: List[Def[?]], terms: List[String]): List[LeanModule] =
    val needs = terms.foldLeft(defs.foldLeft(Needs(ListSet.empty, ListSet.empty))(_.define(_)))(_.term(_))
    needs.defs.toList.map(layout.definition) ++ needs.terms.toList.map(layout.term)

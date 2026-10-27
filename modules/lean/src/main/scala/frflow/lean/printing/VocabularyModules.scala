package frflow
package lean
package printing

import scala.collection.immutable.ListSet
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

  /** A record made of the inputs' fields as they are (`asBooking`: a request's room, start and end): seen through
    * when Lean matches, as where a branch's condition is computed from it. One that computes (`replaceAbout`) stays
    * folded, for the proofs that rewrite with it.
    */
  private def copies(t: Tree): Boolean = t match
    case Tree.Make(_, _, args) =>
      args.forall { case Tree.Field(Tree.Var(_), _, _) | Tree.Var(_) => true; case _ => false }
    case _                     => false

  def files: List[(String, String)] =
    val defs = kb.defs.map { d =>
      // A flow is generic in its monad: any with the boundaries' operations.
      val (monad, tpe) =
        if d.isFlow then (s"{m : Type → Type} [Monad m]${d.lifted.errors.map(e => s" [MonadExceptOf $e m]").mkString}" +
          d.lifted.boundaries.map(b => s" [${b.lean} m]").mkString,
          (d.lifted.params.map(_._2) :+ s"m ${d.lifted.result}").mkString(" → "))
        else ("", d.lifted.leanType)
      val uses = boundariesFor(List(d.lifted)) ++ d.lifted.defs.map(_.name).filter(x => x != d.name && defNames(x)).map(layout.definition)
      layout.definition(d.name).path -> declaring(uses,
        definition(d.name, List(monad, binders(defCtx(d))).filter(_.nonEmpty).mkString(" "), tpe,
          resolve(d.lifted.lean), reducible = copies(d.lifted.built._2.termTree)))
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

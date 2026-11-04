package frflow.proof.terms

import frflow.core.analysis.Resolved
import frflow.core.name.{DefName, NodeId, SymbolName}
import frflow.core.ty.Ty
import frflow.core.vocab.{Symbol, SymbolType}

/** The open terms each declaration is over, in order (a claim, a post, a define), and each symbol's type: what
  * lowering a proposition applies declarations to. Today's `Vocabulary.ctx`, read off the IR.
  */
final case class TermTable(claims: Map[NodeId, OpenTerms], posts: Map[NodeId, OpenTerms],
    defines: Map[DefName, OpenTerms], types: Map[SymbolName, Ty]):
  def typeOf(s: SymbolName): Ty =
    types.getOrElse(s, throw IllegalStateException(s"FrFlow bug: ${s.value} has no type (Validate refuses it)"))

object TermTable:
  def of(r: Resolved): TermTable =
    val t = r.theory
    val defines = t.vocabulary.defines.foldLeft(Map.empty[DefName, OpenTerms])((known, d) =>
      known.updated(d.name, Terms(r, known).of(d.lambda.body, Set(d.name))))
    val terms = Terms(r, defines)
    val nodes = t.refinement.nodes
    TermTable(
      nodes.map(n => n.id -> terms.ofClaim(n.statement)).toMap,
      nodes.flatMap(n => n.statement.call.map(c => n.id -> terms.of(c.posted.value.body))).toMap,
      defines,
      t.vocabulary.symbols.collect { case Symbol(name, _, SymbolType.Typed(ty), _) => name -> ty }.toMap)

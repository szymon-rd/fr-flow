package frflow.proof.terms

import frflow.core.analysis.{Fixed, Resolved}
import frflow.core.expr.{Expr, Lambda}
import frflow.core.name.{DefName, NodeId, SymbolName}
import frflow.core.spec.{Fixing, Statement}
import frflow.core.ty.Ty
import frflow.core.vocab.{Symbol, SymbolType}

/** The open terms each declaration is over, in order (a claim, a post, an expectation, a define), each symbol's type,
  * and what the definitions in force fix terms as: what lowering a proposition applies declarations to. Today's
  * `Vocabulary.ctx` and `Vocabulary.term`, read off the IR.
  */
final case class TermTable(claims: Map[NodeId, OpenTerms], posts: Map[NodeId, OpenTerms],
    expected: Map[(NodeId, Int), OpenTerms], defines: Map[DefName, OpenTerms], types: Map[SymbolName, Ty],
    fixings: Map[Fixed, FixedAs]):
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
      nodes.map(n => n.id -> terms.ofClaim(n.id, n.statement)).toMap,
      nodes.flatMap(n => post(n.statement).map(l => n.id -> terms.of(l.body))).toMap,
      nodes.flatMap(n => expectations(n.statement).zipWithIndex.map((e, i) => (n.id, i) -> terms.of(e))).toMap,
      defines,
      t.vocabulary.symbols.collect { case Symbol(name, _, SymbolType.Typed(ty)) => name -> ty }.toMap,
      r.inForce.fixedBy.flatMap((f, d) => fixing(r, f, d).map(f -> fixedAs(terms, _))))

  private def post(s: Statement): Option[Lambda] = s match
    case Statement.Contract(_, p, _)        => Some(p.post.value)
    case Statement.FlowContract(_, p, _, _) => Some(p.post.value)
    case Statement.AssumedCall(_, p)        => Some(p.post.value)
    case _                                  => None

  private def expectations(s: Statement): List[Expr] = s match
    case Statement.Claim(_, es) => es.map(_.consequence.value)
    case _                      => Nil

  private def fixedAs(terms: Terms, f: Fixing): FixedAs = f match
    case Fixing.TypeAs(_, ty) => FixedAs.Type(ty)
    case Fixing.TermAs(_, l)  => FixedAs.Term(terms.of(l.value.body))

  private def fixing(r: Resolved, f: Fixed, by: NodeId): Option[Fixing] =
    r.theory.node(by).map(_.statement).collect { case Statement.Definition(fs) => fs.toList }.toList.flatten.find {
      case Fixing.TypeAs(sort, _) => f == Fixed.Sort(sort)
      case Fixing.TermAs(sym, _)  => f == Fixed.Term(sym)
    }

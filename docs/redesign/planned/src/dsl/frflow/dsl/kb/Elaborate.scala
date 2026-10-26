package frflow.dsl.kb

import cats.data.{NonEmptyList, ValidatedNec}
import cats.syntax.all.*
import frflow.core.code.{CodeTable, Realization}
import frflow.core.{Elaborated, Sited, Theory}
import frflow.core.graph.Edge
import frflow.core.spec.Node as Spec
import frflow.core.vocab.Vocabulary
import frflow.dsl.build.{Declarations, Deferred, ElabError, Fresh}
import frflow.dsl.node.{Edges, Node}

/** The front end's last phase: the knowledge base as written to the `Theory`. Every part's lambdas are called once
  * on fresh variables, every error is collected, and the vocabulary is what the parts declare.
  */
object Elaborate:
  def apply(kb: KnowledgeBase): ValidatedNec[ElabError, Elaborated] = Fresh.within {
    val attached = kb.code.traverse((id, a) => a.map(id -> _))
    (kb.nodes.traverse(node), attached).tupled.run.map { case (declared, (ns, code)) =>
      val theory = Theory(kb.name, vocabulary(declared), ns.map(_.sited), ns.flatMap(_.edges),
        CodeTable(code.toMap, ns.flatMap(n => NonEmptyList.fromList(n.realized).map(n.sited.node.id -> _)).toMap))
      Elaborated(theory, declared.types.collect { case (n, d :: _) => n -> d.rep }, kb.generators)
    }
  }

  /** One node as elaboration builds it: the node and its position, its edges, the implementations run against it. */
  private final case class Built(sited: Sited, edges: List[Edge], realized: List[Realization])

  private def node(n: Node[?, ?]): Deferred[Built] =
    (n.statement, Edges.of(n.head), n.head.links.realizations.sequence).mapN((s, es, rs) =>
      Built(Sited(Spec(n.head.id, n.head.prose, s), n.head.at), es, rs))

  /** Every declaration of the parts, each once by its value (two of one name both kept, for `Validate`), and the
    * defines elaborated, each define's own declarations included.
    */
  private def vocabulary(d: Declarations): Vocabulary = ???

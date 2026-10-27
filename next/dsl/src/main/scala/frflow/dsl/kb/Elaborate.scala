package frflow.dsl.kb

import cats.data.{NonEmptyList, Validated, ValidatedNec}
import cats.syntax.all.*
import frflow.core.code.{CodeTable, Realization}
import frflow.core.{Elaborated, Sited, Theory}
import frflow.core.expr.{Lambda, OutsideFact}
import frflow.core.graph.Edge
import frflow.core.name.{BoundaryName, DefName}
import frflow.core.spec.{Form, Node as Spec, Written}
import frflow.core.vocab.{Define, DefineForm, Vocabulary}
import frflow.dsl.build.{Declarations, Deferred, ElabError}
import frflow.dsl.node.{Edges, Node}

/** The front end's last phase: the knowledge base as written to the `Theory`. Every part's lambdas are called once
  * on their variables, every error is collected, and the vocabulary is what the parts declare.
  */
object Elaborate:
  def apply(kb: KnowledgeBase): ValidatedNec[ElabError, Elaborated] =
    val attached = kb.code.traverse((id, a) => a.map(id -> _))
    (kb.nodes.traverse(node), attached).tupled.run.andThen { case (declared, (ns, code)) =>
      vocabulary(declared).map { (all, v) =>
        val theory = Theory(kb.name, v, ns.map(_.sited), ns.flatMap(_.edges),
          CodeTable(code.toMap, ns.flatMap(realized).toMap))
        Elaborated(theory, all.types.collect { case (n, d :: _) => n -> d.rep }, kb.generators)
      }
    }

  /** One node as elaboration builds it: the node and its position, its edges, the implementations run against it. */
  private final case class Built(sited: Sited, edges: List[Edge], realized: List[Realization])

  /** The implementations run against a store's model, under the store's name, from the assumption that it behaves
    * as the model.
    */
  private def realized(b: Built): Option[(BoundaryName, NonEmptyList[Realization])] =
    (b.sited.node.statement.outside.collect { case OutsideFact.BehavesAs(store, _) => store },
      NonEmptyList.fromList(b.realized)).tupled

  private def node(n: Node): Deferred[Built] =
    (n.statement, Edges.of(n.head), n.head.links.realizations.sequence).mapN((s, es, rs) =>
      Built(Sited(Spec(n.head.id, n.head.says, s), n.head.at), es, rs))

  /** Every declaration of the parts, each once by its value (two of one name both kept, for `Validate`), and the
    * defines elaborated, each define's own declarations included.
    */
  private def vocabulary(d: Declarations): ValidatedNec[ElabError, (Declarations, Vocabulary)] =
    closed(d).map { (all, defines) =>
      val worlds = all.worlds.values.flatten.toList
      (all, Vocabulary(all.sorts.values.flatten.toList, all.types.values.flatten.map(_.data).toList,
        all.symbols.values.flatten.toList, defines.flatMap(define), worlds.map(_._1), worlds.map(_._2)))
    }

  /** The declarations with every define's own, until no define declares another; and each define elaborated. */
  private def closed(d: Declarations): ValidatedNec[ElabError, (Declarations, List[(DefName, Written[Lambda])])] =
    d.defines.toList.flatMap((n, ls) => ls.map(n -> _)).traverse((n, l) => l.run.map((ds, w) => (ds, n -> w)))
      .andThen { built =>
        val more = d |+| built.foldMap(_._1)
        if more.defines.view.mapValues(_.size).toMap == d.defines.view.mapValues(_.size).toMap then
          Validated.validNec((more, built.map(_._2)))
        else closed(more)
      }

  /** A define, and a program's run on the models beside it (`f_run`, what `impl` is asked of). */
  private def define(n: DefName, w: Written[Lambda]): List[Define] = w.form match
    case Form.Term(_)  => List(Define(n, w, DefineForm.Function))
    case Form.Steps(_) =>
      List(Define(n, w, DefineForm.Flow), Define(DefName(s"${n.value}_run"), w, DefineForm.RunOf(n)))

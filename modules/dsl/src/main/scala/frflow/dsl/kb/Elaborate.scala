package frflow.dsl.kb

import cats.data.{Validated, ValidatedNec}
import cats.syntax.all.*
import frflow.core.{Elaborated, Sited, Theory}
import frflow.core.expr.Lambda
import frflow.core.graph.Edge
import frflow.core.code.{Attachment, CodeTable, Own}
import frflow.core.name.{DefName, SymbolName}
import frflow.core.spec.{Node as Spec, Written}
import frflow.core.typing.IrCheck
import frflow.core.vocab.{Define, DefineForm, ValueKind, Vocabulary}
import frflow.dsl.build.{Declarations, Deferred, ElabError}
import frflow.dsl.node.{Edges, Node}
import frflow.dsl.vocab.Stating

/** The front end's last phase: the FrModel as written to the `Theory`. Every part's lambdas are called once
  * on their variables, every
  * error is collected, and the vocabulary is what the parts declare; the code table is
  * what the FrModel gives each Definition.
  */
object Elaborate:
  def apply(kb: FrModel): ValidatedNec[ElabError, Elaborated] =
    val attached = kb.meanings.traverse((id, a) => a.map(id -> _))
    elaborated(kb, Stating.reading(kb.fixed, kb.held), attached)

  /** The words the model fixes: those it gives a meaning (a Definition listed in it), and
    * those its code calls, read off the model written once with only the first known. A word that is neither is
    * known by the statements alone.
    */
  def fixed(kb: FrModel): Set[SymbolName] =
    val given_ = kb.meanings.map(_._1).toSet
    val written = (kb.nodes.traverse(_.statement(Stating.probing(given_))), kb.meanings.traverse(_._2)).tupled.run
    given_ ++ written.andThen((d, _) => closed(d)).toOption.toList.flatMap(_._1.symbols.collect {
      case (name, ss) if ss.exists(_.kind == ValueKind.Definition) => name })

  private def elaborated(kb: FrModel, stating: Stating, attached: Deferred[List[(SymbolName, Attachment)]])
      : ValidatedNec[ElabError, Elaborated] =
    (kb.nodes.traverse(node(stating, _)), attached).tupled.run.andThen { case (declared, (ns, code)) =>
      vocabulary(declared).map { (all, v) =>
        val theory = IrCheck.checked(Theory(kb.name, v, ns.map(_._1), ns.flatMap(_._2),
          CodeTable(code.toMap, kb.members, kb.reached), kb.writtenIn, Own(all.written, all.referred)))
        Elaborated(theory, all.types.collect { case (n, d :: _) => n -> d.rep }, kb.generators)
      }
    }

  private def node(stating: Stating, n: Node): Deferred[(Sited, List[Edge])] =
    (n.statement(stating), Edges.of(n.head)).mapN((s, es) => (Sited(Spec(n.head.id, n.head.says, s), n.head.at), es))

  /** Every declaration of the parts, each once by its value (two of one name both kept, for `Validate`), and the
    * defines elaborated, each one's own declarations included.
    */
  private def vocabulary(d: Declarations): ValidatedNec[ElabError, (Declarations, Vocabulary)] =
    closed(d).map { (all, defines) =>
      (all, Vocabulary(all.sorts.values.flatten.toList, all.types.values.flatten.map(_.data).toList,
        all.symbols.values.flatten.toList, defines.map((n, w) => Define(n, w, DefineForm.Function))))
    }

  /** The declarations with every define's own, until none declares another; each one elaborated. */
  private def closed(d: Declarations): ValidatedNec[ElabError, (Declarations, List[(DefName, Written[Lambda])])] =
    d.defines.toList.flatMap((n, ls) => ls.map(n -> _)).traverse((n, l) => l.run.map((ds, w) => (ds, n -> w)))
      .andThen { built =>
        val more = d |+| built.foldMap(_._1)
        if sizes(more) == sizes(d) then Validated.validNec((more, built.map(_._2))) else closed(more)
      }

  private def sizes(d: Declarations): Map[DefName, Int] = d.defines.view.mapValues(_.size).toMap

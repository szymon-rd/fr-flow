package frflow.dsl.kb

import cats.data.{Validated, ValidatedNec}
import cats.syntax.all.*
import frflow.core.{Elaborated, Sited, Theory}
import frflow.core.expr.Lambda
import frflow.core.graph.Edge
import frflow.core.name.{DefName, LeanNames, ModelName}
import frflow.core.spec.{Form, Node as Spec, Written}
import frflow.core.typing.IrCheck
import frflow.core.vocab.{Define, DefineForm, StateModel, Vocabulary}
import frflow.dsl.build.{Declarations, Deferred, ElabError}
import frflow.dsl.node.{Edges, Node}

/** The front end's last phase: the FrModel as written to the `Theory`. Every part's lambdas are called once
  * on their variables, every error is collected, and the vocabulary is what the parts declare; the code table is
  * what the FrModel gives each Definition, each operation on a state its model (`Modelled`).
  */
object Elaborate:
  def apply(kb: FrModel): ValidatedNec[ElabError, Elaborated] =
    val attached = kb.meanings.traverse((id, a) => a.map(id -> _))
    (kb.nodes.traverse(node), attached).tupled.run.andThen { case (declared, (ns, code)) =>
      vocabulary(declared).andThen { (all, v) =>
        Modelled.table(v, code.toMap, kb.operations, kb.writtenIn).map { table =>
          val theory = IrCheck.checked(Theory(kb.name, v, ns.map(_._1), ns.flatMap(_._2), table, kb.writtenIn))
          Elaborated(theory, all.types.collect { case (n, d :: _) => n -> d.rep }, kb.generators)
        }
      }
    }

  private def node(n: Node): Deferred[(Sited, List[Edge])] =
    (n.statement, Edges.of(n.head)).mapN((s, es) => (Sited(Spec(n.head.id, n.head.says, s), n.head.at), es))

  /** Every declaration of the parts, each once by its value (two of one name both kept, for `Validate`), and the
    * defines and models elaborated, each one's own declarations included.
    */
  private def vocabulary(d: Declarations): ValidatedNec[ElabError, (Declarations, Vocabulary)] =
    closed(d).map { (all, defines, models) =>
      (all, Vocabulary(all.sorts.values.flatten.toList, all.types.values.flatten.map(_.data).toList,
        all.symbols.values.flatten.toList, defines.flatMap(define), models))
    }

  /** The declarations with every define's and model's own, until none declares another; each one elaborated. */
  private def closed(d: Declarations)
      : ValidatedNec[ElabError, (Declarations, List[(DefName, Written[Lambda])], List[StateModel])] =
    val defines = d.defines.toList.flatMap((n, ls) => ls.map(n -> _))
      .traverse((n, l) => l.run.map((ds, w) => (ds, n -> w)))
    val models = d.models.values.toList.flatten.traverse(_.run)
    (defines, models).tupled.andThen { (built, read) =>
      val more = d |+| built.foldMap(_._1) |+| read.foldMap(_._1)
      if sizes(more) == sizes(d) then Validated.validNec((more, built.map(_._2), read.map(_._2)))
      else closed(more)
    }

  private def sizes(d: Declarations): (Map[DefName, Int], Map[ModelName, Int]) =
    (d.defines.view.mapValues(_.size).toMap, d.models.view.mapValues(_.size).toMap)

  /** A define, and a program's run on the models beside it (`f_run`, what `impl` is asked of). */
  private def define(n: DefName, w: Written[Lambda]): List[Define] = w.form match
    case Form.Term(_)  => List(Define(n, w, DefineForm.Function))
    case Form.Steps(_) =>
      List(Define(n, w, DefineForm.Flow), Define(LeanNames.run(n), w, DefineForm.RunOf(n)))

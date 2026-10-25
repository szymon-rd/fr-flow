package frflow
package lean

import LeanText.*

/** The boundaries in Lean (`FrFlowGen/<KB>/Boundaries.lean`): a class per boundary, its operations over any monad;
  * each model's operations over its own state; `World`, a model's state per field; and each boundary's operations
  * on `StateM World` as its model's, on its field (what proven flows are proven with). Where flows may fail with `E`,
  * also on `ExceptT E (StateM World)`: a failing boundary's call takes the next of the world's `faults` and fails on
  * `true` (`FrFlow.failing`), the others' are lifted.
  */
final class BoundaryModules(kb: KnowledgeBase, layout: Layout, vocabulary: Vocabulary, vocabularyModules: VocabularyModules):
  import vocabulary.*
  private val K = kb.name

  /** The boundaries proven flows call, and those a model is decided for. */
  lazy val boundaries: List[Boundary[?]] =
    (kb.models.map(_.boundary) ++ kb.implementations.flatMap(_.flowDef).flatMap(_.lifted.boundaries)).distinct
  def exist: Boolean = boundaries.nonEmpty

  private def opType(m: java.lang.reflect.Method): (List[(String, frflow.LeanType[?])], frflow.LeanType[?]) =
    (m.getParameters.toList.zip(m.getGenericParameterTypes.toList).map((p, t) => Names.ident(p.getName) -> frflow.LeanType.ofJava(t)),
      frflow.LeanType.ofJava(m.getGenericReturnType))

  /** A model's operation: its steps on the model's state, given its inputs. */
  private def modelOp(mo: ModelOf, m: java.lang.reflect.Method): Lifted[?] =
    val (ps, r) = opType(m)
    Lifted(() => {
      val bs = ps.map((n, t) => Binder(n, t))
      val flow = m.invoke(mo.model, bs.map(_.term[Any])*).asInstanceOf[Flow[?]]
      (bs, Term(Tree.Do(Steps.of(flow)._1), r))
    }, null, "")

  private lazy val ops: List[(ModelOf, java.lang.reflect.Method, Lifted[?])] =
    kb.models.flatMap(mo => mo.boundary.operations.map(m => (mo, m, modelOp(mo, m))))

  def file: String =
    val defs = ops.flatMap(_._3.defs)
    val uses = layout.types :: vocabularyModules.modulesFor(defs, ops.flatMap(o => ctx(o._3).names))
    val classes = boundaries.map { b =>
      s"/-- The boundary ${b.name}: ${b.means}. -/\nclass ${b.lean} (m : Type → Type) where\n" + b.operations.map { m =>
        val (ps, r) = opType(m)
        s"  ${Names.ident(m.getName)} : ${(ps.map(_._2.lean) :+ s"m ${r.lean}").mkString(" → ")}"
      }.mkString("\n")
    }
    val models = kb.models.map { mo =>
      val own = ops.filter(_._1 eq mo).map { (_, m, l) =>
        val tpe = (l.params.map(_._2) :+ s"StateM ${mo.model.stateType.lean} ${l.result}").mkString(" → ")
        definition(Names.ident(m.getName), "", tpe, resolve(l.lean))
      }
      s"namespace ${mo.model.lean}\n\n${own.mkString("\n\n")}\n\nend ${mo.model.lean}"
    }
    val world = "/-- The models' states: what proven flows run on. -/\nstructure World where\n" +
      (kb.models.map(mo => s"  ${mo.model.field} : ${mo.model.stateType.lean}") ++
        Option.when(kb.faulty)("  /-- Which calls of the failing boundaries fail, in order (`true`: that one fails). -/\n  faults : List Bool"))
        .mkString("\n")
    val instances = kb.models.filterNot(_.boundary.fails).map { mo =>
      val f = mo.model.field
      def onWorld(op: String) = s"FrFlow.within (fun w => w.$f) (fun w s => { w with $f := s }) ($op)"
      val members = ops.filter(_._1 eq mo).map { (_, m, l) =>
        val args = l.params.map(_._1)
        s"  ${Names.ident(m.getName)}${args.map(" " + _).mkString} := ${onWorld((s"${mo.model.lean}.${Names.ident(m.getName)}" :: args).mkString(" "))}"
      }
      val lemmas = ops.filter(_._1 eq mo).map { (_, m, l) =>
        val name = Names.ident(m.getName)
        val args = l.params.map(_._1)
        val bs = l.params.map((n, t) => s"($n : $t)").mkString(" ")
        s"@[frflow_defs] theorem ${mo.boundary.lean}.${name}_onWorld${if bs.isEmpty then "" else " " + bs} :\n" +
          s"    ((${(s"${mo.boundary.lean}.$name" :: args).mkString(" ")}) : StateM World ${l.result}) = " +
          s"${onWorld((s"${mo.model.lean}.$name" :: args).mkString(" "))} := rfl"
      }
      s"instance : ${mo.boundary.lean} (StateM World) where\n${members.mkString("\n")}\n\n${lemmas.mkString("\n\n")}"
    }
    val failing = kb.failureType.toList.flatMap { e =>
      val te = frflow.Types.walk(e).lean
      val monad = s"ExceptT $te (StateM World)"
      kb.models.map { mo =>
        val f = mo.model.field
        def onWorld(op: String) =
          val within = s"FrFlow.within (fun w => w.$f) (fun w s => { w with $f := s }) ($op)"
          mo.boundary.failure.fold(s"ExceptT.lift ($within)")(err =>
            s"FrFlow.failing (fun w => w.faults) (fun w fs => { w with faults := fs }) ${frflow.leanOf(err)} ($within)")
        val members = ops.filter(_._1 eq mo).map { (_, m, l) =>
          val args = l.params.map(_._1)
          s"  ${Names.ident(m.getName)}${args.map(" " + _).mkString} := ${onWorld((s"${mo.model.lean}.${Names.ident(m.getName)}" :: args).mkString(" "))}"
        }
        val lemmas = ops.filter(_._1 eq mo).map { (_, m, l) =>
          val name = Names.ident(m.getName)
          val args = l.params.map(_._1)
          val bs = l.params.map((n, t) => s"($n : $t)").mkString(" ")
          s"@[frflow_defs] theorem ${mo.boundary.lean}.${name}_onWorldE${if bs.isEmpty then "" else " " + bs} :\n" +
            s"    ((${(s"${mo.boundary.lean}.$name" :: args).mkString(" ")}) : $monad ${l.result}) = " +
            s"${onWorld((s"${mo.model.lean}.$name" :: args).mkString(" "))} := rfl"
        }
        s"instance : ${mo.boundary.lean} ($monad) where\n${members.mkString("\n")}\n\n${lemmas.mkString("\n\n")}"
      }
    }
    LeanText.module(uses.distinct, K, (classes ++ models ++ Option.when(kb.models.nonEmpty)(world) ++ instances ++ failing).mkString("\n\n") + "\n\n")

  /** The Lean of a model, by operation: what the developer decides of it. */
  def modelText(mo: ModelOf): List[String] =
    ops.filter(_._1 eq mo).map((_, m, l) => s"${Names.ident(m.getName)} = ${resolve(l.lean)}")

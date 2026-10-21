package frflow.model

import frflow.dsl
import frflow.dsl.LayerKind
import frflow.ir.*

final case class AssumptionModel(id: String, name: String, statement: String, justification: String)

/** A law of the theory: `∀ params, body`. */
final case class LawModel(name: String, statement: String, lifted: Lifted)

final case class InvariantModel(name: String, doc: String, requirement: Boolean, lifted: Lifted)

enum TargetModel:
  case Unspecified
  case Skip
  /** Refines operation `op` of layer `layer` (which must be the parent). */
  case Refines(layer: String, op: String, witness: Lifted)

final case class AssumeModel(assumption: String, lifted: Lifted)

final case class OpModel(
    name: String,
    doc: String,
    paramType: Type,
    assumes: List[AssumeModel],
    checks: List[Lifted],
    act: Option[Lifted],
    target: TargetModel
):
  def lifted: List[Lifted] =
    assumes.map(_.lifted) ++ checks ++ act.toList ++ (target match
      case TargetModel.Refines(_, _, w) => List(w)
      case _                         => Nil
    )

enum InitModel:
  /** Abstract layers: a predicate on initial states. */
  case Predicate(code: Lifted)
  /** The implementation: one initial value. */
  case Value(code: Lifted)

  def lifted: Lifted = this match
    case Predicate(l) => l
    case Value(l)     => l

final case class LinkModel(abs: Lifted, glue: Option[Lifted])

final case class LayerModel(
    id: String,
    name: String,
    kind: LayerKind,
    statement: String,
    rationale: String,
    parent: Option[String],
    stateType: Type,
    init: Option[InitModel],
    ops: List[OpModel],
    invariants: List[InvariantModel],
    link: Option[LinkModel],
    cites: List[String]
):
  def isRoot: Boolean = parent.isEmpty
  def op(name: String): Option[OpModel] = ops.find(_.name == name)

  /** Every lifted expression of the layer. */
  def lifted: List[Lifted] =
    init.toList.map(_.lifted) ++ ops.flatMap(_.lifted) ++ invariants.map(_.lifted) ++
      link.toList.flatMap(l => l.abs :: l.glue.toList)

  def assumptionsUsed: List[String] = (cites ++ ops.flatMap(_.assumes.map(_.assumption))).distinct

  /** Types the layer refers to directly. */
  def types: Set[Type] =
    Set(stateType) ++ ops.map(_.paramType) ++ lifted.flatMap(l => l.params.map(_.tpe) :+ l.result)

/** Raised when the DSL objects do not form a valid model (for example, two
  * Scala definitions translate to the same Lean name).
  */
final class ModelError(msg: String) extends RuntimeException(msg)

/** Immutable snapshot of a model: theory, layers and every translated definition. */
final case class TheoryModel(
    name: String,
    domain: List[Type],
    assumptions: List[AssumptionModel],
    laws: List[LawModel],
    layers: List[LayerModel],
    defs: Defs
):
  private lazy val byId: Map[String, LayerModel] = layers.map(l => l.id -> l).toMap

  def layer(id: String): Option[LayerModel] = byId.get(id)
  def layerOrFail(id: String): LayerModel =
    byId.getOrElse(id, throw new NoSuchElementException(s"Unknown layer '$id' in model '$name'"))
  def roots: List[LayerModel] = layers.filter(_.isRoot)
  def children(id: String): List[LayerModel] = layers.filter(_.parent.contains(id))
  def parentOf(l: LayerModel): Option[LayerModel] = l.parent.flatMap(byId.get)
  def assumption(id: String): Option[AssumptionModel] = assumptions.find(_.id == id)

  /** Ancestors from the direct parent up to the root. */
  def ancestors(l: LayerModel): List[LayerModel] =
    def loop(cur: LayerModel, seen: Set[String]): List[LayerModel] =
      parentOf(cur) match
        case Some(p) if !seen(p.id) => p :: loop(p, seen + p.id)
        case _                      => Nil
    loop(l, Set(l.id))

  def pathFromRoot(l: LayerModel): List[LayerModel] = (l :: ancestors(l)).reverse

  /** Layers ordered so that every parent precedes its children. */
  def topological: List[LayerModel] = layers.sortBy(l => ancestors(l).size)

  /** Definitions reachable from a set of types and expressions, in dependency order. */
  def closure(types: Iterable[Type], exprs: Iterable[Expr]): List[String] =
    val seen = scala.collection.mutable.LinkedHashSet.empty[String]
    def visitName(n: String): Unit =
      if !seen(n) then
        defs.adts.get(n) match
          case Some(a) =>
            seen += n
            a.references.foreach(visitName)
          case None =>
            defs.funs.get(n).foreach { f =>
              seen += n
              f.references.foreach(visitName)
              f.body.calls.foreach(visitName)
            }
    types.foreach(_.references.foreach(visitName))
    exprs.foreach { e =>
      e.calls.foreach(visitName)
      e.subterms.foreach {
        case Expr.Lam(ps, _)      => ps.foreach(_.tpe.references.foreach(visitName))
        case Expr.Quant(_, ps, _) => ps.foreach(_.tpe.references.foreach(visitName))
        case Expr.Let(_, t, _, _) => t.references.foreach(visitName)
        case Expr.PrimOp(_, _, t) => t.foreach(_.references.foreach(visitName))
        case Expr.Construct(c, _) => adtOfCtor(c).foreach(visitName)
        case _                    => ()
      }
    }
    seen.toList

  /** The ADT a constructor name belongs to (`UserId.mk` → `UserId`, `Action.Read` → `Action`). */
  def adtOfCtor(ctor: String): Option[String] =
    val owner = ctor.substring(0, ctor.lastIndexOf('.').max(0))
    defs.adts.get(owner).map(_.name)

  /** Definitions a layer depends on. */
  def layerDefs(l: LayerModel): List[String] =
    closure(l.types, l.lifted.map(_.body))

  /** Definitions the theory node consists of: the declared domain types, their
    * methods and companion values, and everything the laws use.
    */
  def theoryDefs: List[String] =
    val types = domain ++ laws.flatMap(l => l.lifted.params.map(_.tpe))
    val bodies = laws.map(_.lifted.body)
    val adts = closure(types, bodies).filter(defs.adts.contains).toSet
    val members = defs.funs.keys.toList.sorted.filter(n => adts(n.substring(0, n.lastIndexOf('.').max(0))))
    closure(types, bodies ++ members.map(Expr.Ref(_)))

  /** All definitions in dependency order (dependencies first). */
  def orderedDefs: List[String] =
    val all = defs.adts.keys.toList.sorted ++ defs.funs.keys.toList.sorted
    val visited = scala.collection.mutable.LinkedHashSet.empty[String]
    val onStack = scala.collection.mutable.Set.empty[String]
    def deps(n: String): List[String] =
      defs.adts.get(n).map(_.references.toList.sorted).orElse(
        defs.funs.get(n).map(f => (f.references ++ f.body.calls - n).toList.sorted)
      ).getOrElse(Nil).filter(d => defs.adts.contains(d) || defs.funs.contains(d))
    def visit(n: String): Unit =
      if !visited(n) && !onStack(n) then
        onStack += n
        deps(n).foreach(visit)
        onStack -= n
        visited += n
    all.foreach(visit)
    visited.toList

object TheoryModel:

  /** Builds the snapshot of a DSL model. */
  def from(m: dsl.Model): TheoryModel =
    val theory = m.theory
    var defs = Defs.empty
    val origin = scala.collection.mutable.Map.empty[String, String]

    def absorb(r: LiftResult): Unit =
      def check(name: String, scalaName: String): Unit =
        origin.get(name) match
          case Some(o) if o != scalaName =>
            throw ModelError(s"$o and $scalaName both translate to the Lean name $name; rename one of them")
          case _ => origin(name) = scalaName
      r.defs.adts.values.foreach(a => check(a.name, a.scalaName))
      r.defs.funs.values.foreach(f => check(f.name, f.scalaName))
      defs = defs ++ r.defs

    def lift(c: frflow.lift.Code[?]): Lifted =
      absorb(c.ir)
      c.lifted

    def typeOf(s: frflow.lift.Schema[?]): Type =
      absorb(s.ir)
      s.ir.tpe

    val domain = theory.domainSchemas.flatMap { s =>
      typeOf(s) match
        case Type.TupleOf(ts) => ts
        case t                => List(t)
    }
    val laws = theory.laws.map(l => LawModel(l.name, l.statement, lift(l.code)))
    val assumptions = theory.assumptions.map(a => AssumptionModel(a.id, a.name, a.statement, a.justification))

    val layers = m.layers.map { layer =>
      val ops = layer.operations.map { op =>
        val target = op.target match
          case dsl.OpTarget.Unspecified          => TargetModel.Unspecified
          case dsl.OpTarget.Skip                 => TargetModel.Skip
          case dsl.OpTarget.Refines(parent, w)   => TargetModel.Refines(parent.layer.id, parent.name, lift(w))
        OpModel(
          op.name, op.doc, typeOf(op.paramSchema),
          op.assumes.toList.map((a, c) => AssumeModel(a.id, lift(c))),
          op.checks.toList.map(lift), op.action.map(lift), target
        )
      }
      val invs = layer.invariants.map(i => InvariantModel(i.name, i.doc, i.requirement, lift(i.code)))
      val (init, link) = layer match
        case l: dsl.Requirements[?]      => (l.initial.map(c => InitModel.Predicate(lift(c))), None)
        case l: dsl.Refinement[?, ?]     =>
          (l.initial.map(c => InitModel.Predicate(lift(c))), l.abstractionCode.map(a => LinkModel(lift(a), l.glueInvariant.map(lift))))
        case l: dsl.Implementation[?, ?] =>
          (l.initialState.map(c => InitModel.Value(lift(c))), l.abstractionCode.map(a => LinkModel(lift(a), l.glueInvariant.map(lift))))
      LayerModel(
        layer.id, layer.name, layer.kind, layer.statement, layer.rationale, layer.parentLayer.map(_.id),
        typeOf(layer.stateSchema), init, ops, invs, link, layer.cited.map(_.id)
      )
    }
    TheoryModel(theory.name, domain, assumptions, laws, layers, defs)

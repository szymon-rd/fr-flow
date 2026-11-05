package frflow.core.analysis.outside

import cats.syntax.all.*
import frflow.core.analysis.resolution.{Callees, Constrained, Resolve, SaysWhat}
import frflow.core.analysis.outside.Scope
import frflow.core.code.Code
import frflow.core.expr.{Expr, Exprs, Quantifier}
import frflow.core.graph.Walk
import frflow.core.name.{ModelName, NodeId, SymbolName}
import frflow.core.spec.{Node, NodeKind, Range}
import frflow.core.Theory
import frflow.core.ty.Ty
import frflow.core.vocab.SymbolType

/** The one World kept local (owner §33): a statement reads only some stores, and takes only their rules as hypotheses
  * on the worlds it is about, so adding a store changes no statement that does not read it. A statement reads the
  * models whose state it mentions (through its defines), those of the operations the proven code standing in it calls,
  * and, for each Declaration it mentions, those the claims saying what that Declaration is read: a root over
  * Declarations reads the world as they are said to.
  */
object Reads:
  def models(t: Theory, id: NodeId): List[ModelName] =
    val meanings = Constrained.of(t, id).filter(Constrained.isDeclaration(t, _)).flatMap(saying(t, _))
    (direct(t, id) ++ meanings.filterNot(_ == id).flatMap(direct(t, _))).distinct

  /** The models a program reads and writes: those of the operations it calls. */
  def ofProgram(t: Theory, op: SymbolName): List[ModelName] =
    Callees.ofDefinition(t, op).toList.flatMap(_.calls.operations).flatMap(stored(t, _)).distinct

  /** Whether `id` takes the rule `rule` as a hypothesis: the rule's guard applies to a type the statement quantifies
    * over, or, of a world it quantifies over, to a store it reads.
    */
  def takes(t: Theory, id: NodeId, rule: NodeId): Boolean =
    guarded(t, id, rule) || fromOutside(t, id, rule)

  /** Whether `id` rests on the rule: it is the rule, or a claim taking it (`takes`) is, or is among what it is proven
    * from, all the way down (`Resolve.below`): that claim is proven only once the rule is, whose `cover_` then could
    * not take it. An assumption taking the rule is trusted, proven from nothing, so it rests on nothing.
    */
  def restsOn(t: Theory, id: NodeId, rule: NodeId): Boolean =
    Walk.breadthFirst(List(id), identity)(Resolve.below(t, _)).exists(h => h == rule ||
      (t.node(h).exists(_.statement.kind != NodeKind.Assumption) && takes(t, h, rule)))

  /** The rules an obligation takes as given on values of `inputs` and on a world of `models` (`Guarded`): each rule
    * about one of those stores, and each `always[T]` whose `T` an input holds (`Guards.applies`). What each kind of
    * obligation takes is `Obligations.takes`' (the step 13d third pass's R3-B1).
    */
  def rulesAt(t: Theory, inputs: List[Ty], models: List[ModelName]): List[NodeId] =
    t.nodes.map(_.node).filter(_.statement.rule).filter(_.statement.range.exists { r =>
      Scope.models(t, r).map(_.name).exists(models.contains) || (r match
        case Range.Made(ty) => inputs.exists(Guards.applies(t, ty, _))
        case _              => false)
    }).map(_.id)

  /** What `cover_<op>` takes on the world a run starts from (`Required.keeps`): the rules on the stores the program
    * reads and on its inputs; of the world's own step (`elapse`, `Required.outside`), every rule on a store.
    */
  def coverTaken(t: Theory, op: SymbolName): List[NodeId] =
    if t.vocabulary.modelOf(op).nonEmpty then rulesAt(t, Nil, t.vocabulary.models.map(_.name))
    else rulesAt(t, inputs(t, op), ofProgram(t, op))

  /** The types of a Definition's inputs. */
  def inputs(t: Theory, op: SymbolName): List[Ty] = t.vocabulary.symbol(op).map(_.ty).toList.flatMap {
    case SymbolType.Typed(Ty.FnOf(ins, _)) => ins
    case _                                 => Nil
  }

  /** Of a statement, the rules its claim takes (`takes`, its `Lowering.guards`), and the value rules the `forall`s of
    * the defines it mentions come with (`VocabularyModules.guards`): a define read in Lean means what it does only
    * where those rules hold.
    */
  def taken(t: Theory, id: NodeId): List[NodeId] =
    val said = t.node(id).flatMap(_.statement.said).toList.flatMap(f => Exprs.mentions(f.value).defines)
    val over = t.vocabulary.closure(said).flatMap(d => Exprs.all(d.lambda.body).collect {
      case Expr.Quant(Quantifier.Forall | Quantifier.Exists, xs, _) => xs.map(_.ty)
    }.flatten).filterNot(_ == Ty.World)
    t.nodes.map(_.node).filter(r => r.id != id && r.statement.rule).filter(r => takes(t, id, r.id) ||
      r.statement.range.exists {
        case Range.Made(ty) => over.exists(Guards.applies(t, ty, _))
        case _              => false
      }).map(_.id)

  private def guarded(t: Theory, id: NodeId, rule: NodeId): Boolean =
    (t.node(id), t.node(rule).flatMap(_.statement.range)).tupled.exists { (n, r) =>
      val over = quantified(n) ++ provided(t, id).map(_._2)
      val worlds = over.contains(Ty.World) && Scope.models(t, r).map(_.name).exists(models(t, id).contains)
      worlds || (r match
        case Range.Made(ty) => over.exists(x => x != Ty.World && Guards.applies(t, ty, x))
        case _              => false)
    }

  /** An assumption of `always[U]` a statement's check rests on (`Premises`: its Lean or its obligations carry it). */
  private def fromOutside(t: Theory, id: NodeId, rule: NodeId): Boolean = t.node(rule).exists(a =>
    Outsides.aboutOutside(a) && Premises.of(t, id).exists(Outsides.saysOf(a, _)))

  /** The types of the variables a statement's formula quantifies over, or binds as a run's outcome and world. */
  def quantified(n: Node): List[Ty] = n.statement.said.toList.flatMap(f => Exprs.all(f.value).collect {
    case Expr.Quant(Quantifier.Forall | Quantifier.Exists, xs, _) => xs.map(_.ty)
  }.flatten)

  /** The values provided where the code runs that a statement mentions, through its defines, with their types: values
    * from outside (owner §21), each with what always holds of its type as a hypothesis, as a variable has.
    */
  def provided(t: Theory, id: NodeId): List[(SymbolName, Ty)] =
    Constrained.of(t, id).filter(s => t.code.attached.get(s).exists(_.code == Code.Provided)).flatMap(s =>
      t.vocabulary.symbol(s).map(_.ty).collect { case SymbolType.Typed(ty) => s -> ty })

  private def direct(t: Theory, id: NodeId): List[ModelName] =
    Resolve.mentions(t, id).models ++
      Callees.of(t, id).toList.flatMap(_.calls.operations).flatMap(stored(t, _))

  private def saying(t: Theory, d: SymbolName): List[NodeId] =
    t.nodes.map(_.node.id).filter(SaysWhat.declarations(t, _).contains(d))

  private def stored(t: Theory, op: SymbolName): List[ModelName] = t.vocabulary.modelOf(op).map(_.name).toList

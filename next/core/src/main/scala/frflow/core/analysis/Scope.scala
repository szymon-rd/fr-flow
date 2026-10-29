package frflow.core.analysis

import frflow.core.name.{NodeId, SymbolName, TypeName}
import frflow.core.spec.Range
import frflow.core.Theory
import frflow.core.ty.Ty
import frflow.core.vocab.{OpSig, StateModel, SymbolType}
import frflow.core.analysis.outside.Guards

/** Where a claim of `always` must hold, each Definition there keeping it (owner §16: wherever FrFlow covers the
  * code). Of `always[T](…)`: the Definitions whose result can hold a `T` (where a value is made) and the programs
  * calling an operation on a state that can; of `always(stored)(…)`: the programs calling the model's operations. An
  * operation on a state is held to it on its model instead (`modelMakers`). An assumption of
  * `always` is held here as a claim is: it stands only for the values no covered code makes (owner §21: an entry
  * Definition's inputs, the values provided where the code runs), so the code that makes or stores its values keeps
  * it (`made_`, `cover_`). A type holds a value of another when it names it or a type whose fields hold it.
  */
object Scope:
  def of(t: Theory, always: NodeId): List[SymbolName] =
    t.node(always).flatMap(_.statement.range).collect {
      case r @ (Range.Made(_) | Range.Reached(_)) =>
        val stores = models(t, r).flatMap(_.ops.map(_.op)).toSet
        val ops = t.vocabulary.symbols.map(_.name).filter(Constrained.isFunction(t, _))
          .filterNot(s => Constrained.isDeclaration(t, s) || t.vocabulary.modelOf(s).nonEmpty)
        ops.filter(op => makes(t, r, op) || calls(t, stores, op))
    }.getOrElse(Nil)

  /** The models whose state an `always` is about: those its rule reads, or each one whose state can hold its type. */
  def models(t: Theory, r: Range): List[StateModel] = r match
    case Range.Reached(ms) => ms.flatMap(t.vocabulary.model)
    case Range.Made(ty)    => t.vocabulary.models.filter(m => holds(t, ty, m.state))
    case Range.Possible    => Nil

  /** The operations on a state whose result `always[T]`'s guard applies to (a `T`, a list of them, a record holding
    * either), by their model: where its values are made by the models FrFlow covers (`made_<op>`).
    */
  def modelMakers(t: Theory, r: Range): List[(StateModel, OpSig)] = r match
    case Range.Made(ty) =>
      for
        m   <- t.vocabulary.models
        sig <- m.sigs if Guards.applies(t, ty, sig.result)
      yield m -> sig
    case _              => Nil

  /** The claims of `always` a Definition keeps. */
  def keeps(t: Theory, op: SymbolName): List[NodeId] = t.nodes.map(_.node.id).filter(of(t, _).contains(op))

  /** `ty` can hold a value of `about`. */
  def holds(t: Theory, about: Ty, ty: Ty): Boolean = Ty.names(about).exists(named(t, _, ty, Set.empty))

  private def makes(t: Theory, r: Range, op: SymbolName): Boolean = r match
    case Range.Made(ty) =>
      t.vocabulary.symbol(op).map(_.ty).collect { case SymbolType.Typed(f) => Ty.resultOf(f) }.exists(holds(t, ty, _))
    case _              => false

  private def calls(t: Theory, operations: Set[SymbolName], op: SymbolName): Boolean =
    Callees.ofDefinition(t, op).exists(_.calls.operations.exists(operations))

  private def named(t: Theory, about: TypeName, ty: Ty, seen: Set[TypeName]): Boolean =
    val names = Ty.names(ty)
    names.contains(about) || names.filterNot(seen).exists(n =>
      t.vocabulary.dataType(n).exists(_.fieldTypes.exists(named(t, about, _, seen + n))))

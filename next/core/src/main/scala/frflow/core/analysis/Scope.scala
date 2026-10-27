package frflow.core.analysis

import frflow.core.name.{BoundaryName, NodeId, SymbolName, TypeName}
import frflow.core.spec.Range
import frflow.core.Theory
import frflow.core.ty.Ty
import frflow.core.vocab.{OpSig, StateModel, SymbolType}

/** Where a claim of `always` must hold, each Definition there keeping it (owner §16: wherever FrFlow covers the
  * code). Of `always[T](…)`: the Definitions whose result can hold a `T` (where a value is made) and the programs
  * calling a store whose state can; of `always(stored)(…)`: the programs calling the store. An assumption of
  * `always` is held here as a claim is: it stands only for the values no covered code makes (owner §21: an entry
  * Definition's inputs, the values provided where the code runs), so the code that makes or stores its values keeps
  * it (`made_`, `cover_`). A type holds a value of another when it names it or a type whose fields hold it.
  */
object Scope:
  def of(t: Theory, always: NodeId): List[SymbolName] =
    t.node(always).flatMap(_.statement.range).collect {
      case r @ (Range.Made(_) | Range.Reached(_)) =>
        val boundaries = models(t, r).map(_.boundary).toSet
        val ops = t.vocabulary.symbols.map(_.name).filter(Constrained.isFunction(t, _))
          .filterNot(Constrained.isDeclaration(t, _))
        ops.filter(op => makes(t, r, op) || calls(t, boundaries, op))
    }.getOrElse(Nil)

  /** The models whose state an `always` is about: those its rule reads, or each one whose state can hold its type. */
  def models(t: Theory, r: Range): List[StateModel] = r match
    case Range.Reached(ms) => ms.flatMap(t.vocabulary.model)
    case Range.Made(ty)    => t.vocabulary.models.filter(m => holds(t, ty, m.state))
    case Range.Possible    => Nil

  /** The store operations whose result `always[T]`'s guard applies to (a `T`, a list of them, a record holding
    * either), by the store's model: where its values are made by the models FrFlow covers (`made_<op>`).
    */
  def modelMakers(t: Theory, r: Range): List[(StateModel, OpSig)] = r match
    case Range.Made(ty) =>
      for
        m   <- t.vocabulary.models
        b   <- t.vocabulary.boundary(m.boundary).toList
        sig <- b.ops if Guards.applies(t, ty, sig.result)
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

  private def calls(t: Theory, boundaries: Set[BoundaryName], op: SymbolName): Boolean =
    Callees.ofDefinition(t, op).exists(_.calls.boundaries.exists(boundaries))

  private def named(t: Theory, about: TypeName, ty: Ty, seen: Set[TypeName]): Boolean =
    val names = Ty.names(ty)
    names.contains(about) || names.filterNot(seen).exists(n =>
      t.vocabulary.dataType(n).exists(_.fieldTypes.exists(named(t, about, _, seen + n))))

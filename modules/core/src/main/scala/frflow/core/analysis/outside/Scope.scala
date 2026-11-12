package frflow.core.analysis.outside

import frflow.core.analysis.resolution.Constrained
import frflow.core.name.{NodeId, SymbolName, TypeName}
import frflow.core.spec.Range
import frflow.core.Theory
import frflow.core.ty.Ty
import frflow.core.vocab.SymbolType

/** Where a claim of `always` must hold, each Definition there keeping it (owner §16: wherever FrFlow covers the
  * code). Of `always[T](…)`: the Definitions whose result can hold a `T` (where a value is made). An assumption of
  * `always` is held here as a claim is: it stands only for the values no covered code makes (owner §21: an entry
  * Definition's inputs, the values provided where the code runs), so the code that makes its values keeps it
  * (`made_`, `cover_`). A type holds a value of another when it names it or a type whose fields hold it.
  */
object Scope:
  def of(t: Theory, always: NodeId): List[SymbolName] =
    t.node(always).flatMap(_.statement.range).collect {
      case Range.Made(ty) =>
        t.vocabulary.symbols.map(_.name).filter(Constrained.isFunction(t, _))
          .filterNot(Constrained.isDeclaration(t, _)).filter(makes(t, ty, _))
    }.getOrElse(Nil)

  /** The claims of `always` a Definition keeps. */
  def keeps(t: Theory, op: SymbolName): List[NodeId] = t.nodes.map(_.node.id).filter(of(t, _).contains(op))

  /** `ty` can hold a value of `about`. */
  def holds(t: Theory, about: Ty, ty: Ty): Boolean = Ty.names(about).exists(named(t, _, ty, Set.empty))

  private def makes(t: Theory, ty: Ty, op: SymbolName): Boolean =
    t.vocabulary.symbol(op).map(_.ty).collect { case SymbolType.Typed(f) => Ty.resultOf(f) }.exists(holds(t, ty, _))

  private def named(t: Theory, about: TypeName, ty: Ty, seen: Set[TypeName]): Boolean =
    val names = Ty.names(ty)
    names.contains(about) || names.filterNot(seen).exists(n =>
      t.vocabulary.dataType(n).exists(_.fieldTypes.exists(named(t, about, _, seen + n))))

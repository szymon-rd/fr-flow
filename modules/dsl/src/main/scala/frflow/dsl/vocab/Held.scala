package frflow.dsl.vocab

import frflow.core.name.SymbolName
import frflow.core.ty.Ty

/** Which structures a model has held by which: for a structure's word, each structure whose class is given it,
  * with the word that is what that holder holds as it (`basket_holds_pricing`: from a state of the holder, the
  * state of what it holds). Holding composes: what a counter's basket holds, the counter holds through it.
  */
final case class Held(by: Map[SymbolName, Map[SymbolName, Definition[?]]]):
  /** Each way down to `part` from a holder `top` accepts, the nearest one on each way up: the holder, and the
    * words to apply to a state of it, in order (`counter_holds_basket`, then `basket_holds_pricing`).
    */
  def ways(part: SymbolName)(top: (SymbolName, Definition[?]) => Boolean): List[Held.Way] =
    def up(of: SymbolName, seen: Set[SymbolName]): List[Held.Way] =
      by.getOrElse(of, Map.empty).toList.sortBy(_._1.value).flatMap { (holder, via) =>
        if top(holder, via) then List(Held.Way(holder, List(via)))
        else if seen(holder) then Nil
        else up(holder, seen + holder).map(w => w.copy(through = w.through :+ via))
      }
    up(part, Set(part))

object Held:
  val none: Held = Held(Map.empty)

  /** A way down from a holder to what it holds: the holder's word, and the words applied to a state of it, the
    * holder's own first.
    */
  final case class Way(holder: SymbolName, through: List[Definition[?]])

  /** The type of the holder's states and of the held structure's, as the word between them is typed. */
  def ends(via: Definition[?]): (Ty, Ty) = via.rocqType.ty match
    case Ty.FnOf(List(holder), part) => (holder, part)
    case other                       => throw IllegalStateException(s"FrFlow bug: ${via.name.value} is a $other")

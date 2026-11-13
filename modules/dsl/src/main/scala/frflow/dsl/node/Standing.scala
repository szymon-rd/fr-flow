package frflow.dsl.node

import frflow.core.name.SymbolName
import frflow.dsl.build.{Failure, Fault}
import frflow.dsl.structure.Call
import frflow.dsl.term.{RocqType, Notes, Term, Terms}
import frflow.dsl.vocab.{Held, Stating}
import scala.collection.mutable

/** A statement over the structures it reads as they stand: said of each structure in every state. The structures are
  * found by writing the statement once and reading it open (`Closing.opened`); it is then written under a `forall` for
  * each, the structure read as that variable. So a claim on a structure is one a class that uses the structure can rely
  * on, whatever state it holds it in. A structure read beside one that holds it (`ledger.total` beside
  * `handler.handle(p)`) is the one held: no variable of its own, but what the holder's variable holds. So is one read
  * beside a structure that holds its holder: what a counter's basket holds, the counter holds through it. A statement
  * that reads no structure is written as it always was.
  */
object Standing:
  def closing(st: Stating, formula: Stating => () => Term[Boolean]): Term[Boolean] =
    val read = mutable.LinkedHashMap.empty[SymbolName, RocqType[?]]
    Notes.in(Closing.opened(formula(st.asking((name, t) => read.update(name, t)))())).discard
    if read.isEmpty then formula(st)()
    else
      val holders = read.keys.toList.flatMap(part => holder(st, part, read.keySet).map(part -> _)).toMap
      val written = (bound: Map[SymbolName, Term[?]]) => formula(st.holding(held(read.keySet, holders, bound)))()
      read.toList.filterNot((name, _) => holders.contains(name)).foldRight(written) { case ((name, t), inner) =>
        bound => Terms.forall[Any](name.value, (v: Term[Any]) => inner(bound + (name -> v)))(
          using t.asInstanceOf[RocqType[Any]])
      }(Map.empty)

  /** The way to `part` from the structure read here that holds it, itself or through what it holds, if one does;
    * refused of two.
    */
  private def holder(st: Stating, part: SymbolName, read: collection.Set[SymbolName]): Option[Held.Way] =
    st.held.ways(part)((holder, _) => read.contains(holder)) match
      case Nil       => None
      case List(one) => Some(one)
      case several   => throw Failure(several.map(_.holder.value).distinct match
        case List(_) => Fault.HeldTwice(part.value, several.map(_.through.map(_.name.value)))
        case holders => Fault.HeldByTwo(part.value, holders))

  /** Each structure read as it stands: its variable, or, of one held, what its holder's holds. */
  private def held(read: collection.Set[SymbolName], holders: Map[SymbolName, Held.Way],
      bound: Map[SymbolName, Term[?]]): Map[SymbolName, Term[?]] =
    def of(name: SymbolName): Term[?] = holders.get(name).fold(bound(name))(way => Call.through(way, of(way.holder)))
    read.map(name => name -> of(name)).toMap

  extension (x: Any) private def discard: Unit = ()

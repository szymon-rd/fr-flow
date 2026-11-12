package frflow.dsl.node

import frflow.core.name.SymbolName
import frflow.dsl.term.{LeanType, Notes, Term, Terms}
import frflow.dsl.vocab.Stating
import scala.collection.mutable

/** A statement over the services it reads as they stand: said of each service in every state. The services are
  * found by writing the statement once and reading it open, as what changes with the World is read off one
  * (`Closing.opened`); it is then written under a `forall` for each, the service read as that variable. So a claim
  * on a service is one a class that uses the service can rely on, whatever state it holds it in. A statement that
  * reads no service is written as it always was.
  */
object Serving:
  def closing(st: Stating, formula: Stating => () => Term[Boolean]): Term[Boolean] =
    val read = mutable.LinkedHashMap.empty[SymbolName, LeanType[?]]
    Notes.in(Closing.opened(formula(st.asking((name, t) => read.update(name, t)))())).discard
    val written = (bound: Map[SymbolName, Term[?]]) => formula(st.holding(bound))()
    if read.isEmpty then formula(st)()
    else read.toList.foldRight(written) { case ((name, t), inner) =>
      bound => Terms.forall[Any](name.value, (v: Term[Any]) => inner(bound + (name -> v)))(
        using t.asInstanceOf[LeanType[Any]])
    }(Map.empty)

  extension (x: Any) private def discard: Unit = ()

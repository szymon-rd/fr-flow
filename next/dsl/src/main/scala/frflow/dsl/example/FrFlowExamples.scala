package frflow.dsl.example

import cats.data.ValidatedNec
import cats.syntax.all.*
import frflow.core.example.Example as Elaborated
import frflow.dsl.build.{ElabError, Site, Source}
import frflow.dsl.kb.FrModel
import frflow.dsl.node.Node
import frflow.dsl.shape.Elab
import frflow.dsl.build.Fault
import frflow.dsl.kb.Varying
import frflow.dsl.run.Worlds
import frflow.dsl.term.{Notes, Term}
import frflow.dsl.vocab.Stating
import scala.collection.mutable.ListBuffer

/** A model's examples, written as an ordinary test file writes them, as today's library does (owner §18):
  * {{{
  * class GrantedExamples extends FrFlowExamples(rooms):
  *   example("back to back: granted"):
  *     granted(RoomBookings(List(Booking("Oak", 9, 10))), Booking("Oak", 10, 11)) is true
  * }}}
  * Each `example` registers one as the class is built, as a test suite registers its tests; FrFlow reads them beside
  * the FrModel, checks each against the code and, where it sets no value, against the claims in Lean. They
  * show how things work; nothing in the FrModel depends on them.
  */
abstract class FrFlowExamples(val knowledge: FrModel):
  private val written = ListBuffer.empty[Example]

  /** One example: its name, the values it gives provided Definitions, its fact. */
  protected inline def example(name: String, bindings: Binding*)(inline fact: Stating ?=> Term[Boolean]): Unit =
    register(Example(name, bindings.toList,
      Elab.formula(Site.Example(name), () => worldless(fact(using stating)), Source.of(Node.writing(fact)))))

  /** What changes with the World in the FrModel, so a Declaration is applied as its statements apply it. */
  protected lazy val stating: Stating =
    Stating.varying(Varying.of(knowledge.nodes).getOrElse(Set.empty))

  /** An example's fact is a closed fact about the code, read in no world: one reading what changes with the World
    * (a model's state, a run, a Declaration that changes) is refused.
    */
  protected def worldless(fact: Term[Boolean]): Term[Boolean] =
    if Worlds.reads(fact).contains(false) then fact
    else Term.noted(Notes.fault(Fault.WorldRead("an example")))(fact.run)

  protected def register(e: Example): Unit = written += e

  /** The examples, in the order written. */
  def examples: List[Example] = written.toList
  lazy val elaborated: ValidatedNec[ElabError, List[Elaborated]] = examples.traverse(_.elaborated).run.map(_._2)

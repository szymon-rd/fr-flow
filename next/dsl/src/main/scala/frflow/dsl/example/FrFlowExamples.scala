package frflow.dsl.example

import cats.data.ValidatedNec
import cats.syntax.all.*
import frflow.core.example.Example as Elaborated
import frflow.dsl.build.{ElabError, Site, Source}
import frflow.dsl.kb.KnowledgeBase
import frflow.dsl.node.Node
import frflow.dsl.shape.Elab
import frflow.dsl.term.Term
import frflow.dsl.vocab.Stating
import scala.collection.mutable.ListBuffer

/** A model's examples, written as an ordinary test file writes them, as today's library does (owner §18):
  * {{{
  * class GrantedExamples extends FrFlowExamples(rooms):
  *   example("back to back: granted"):
  *     granted(RoomBookings(List(Booking("Oak", 9, 10))), Booking("Oak", 10, 11)) is true
  * }}}
  * Each `example` registers one as the class is built, as a test suite registers its tests; FrFlow reads them beside
  * the knowledge base, checks each against the code and, where it sets no value, against the claims in Lean. They
  * show how things work; nothing in the knowledge base depends on them.
  */
abstract class FrFlowExamples(val knowledge: KnowledgeBase):
  private val written = ListBuffer.empty[Example]

  /** One example: its name, the values it gives provided Definitions, its fact. */
  protected inline def example(name: String, bindings: Binding*)(inline fact: Stating ?=> Term[Boolean]): Unit =
    register(Example(name, bindings.toList,
      Elab.formula(Site.Example(name), () => fact(using Stating.writing), Source.of(Node.writing(fact)))))

  protected def register(e: Example): Unit = written += e

  /** The examples, in the order written. */
  def examples: List[Example] = written.toList
  lazy val elaborated: ValidatedNec[ElabError, List[Elaborated]] = examples.traverse(_.elaborated).run.map(_._2)

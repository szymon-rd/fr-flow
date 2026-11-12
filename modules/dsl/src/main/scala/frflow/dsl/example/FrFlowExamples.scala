package frflow.dsl.example

import cats.data.{NonEmptyChain, Validated, ValidatedNec}
import cats.syntax.all.*
import frflow.core.expr.{Expr, Exprs}
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
    Stating.varying(Varying.of(knowledge.nodes, knowledge.fixed).getOrElse(Set.empty), knowledge.fixed)

  /** An example's fact is a closed fact about the code, read in no world: one reading what changes with the World
    * (a model's state, a run, a Declaration that changes) is refused.
    */
  protected def worldless(fact: Term[Boolean]): Term[Boolean] =
    val constant = Term.exprOf(fact).exists(e => Exprs.all(e).exists {
      case Expr.Constant(_, _, _) => true
      case _                      => false
    })
    if Worlds.reads(fact).contains(false) then fact
    else Term.noted(Notes.fault(if constant then Fault.ConstantInside("in an example") else
      Fault.WorldRead("an example")))(fact.run)

  protected def register(e: Example): Unit = written += e

  /** The examples, in the order written. */
  def examples: List[Example] = written.toList
  /** The set's name, as each example's obligation is named (`example_<set>_<i>`): the class's, as a Lean identifier
    * (`FrFlowExamples.identifier`).
    */
  def setName: String = FrFlowExamples.identifier(getClass.getSimpleName.stripSuffix("$"), getClass.getName)
  lazy val elaborated: ValidatedNec[ElabError, List[Elaborated]] =
    examples.zipWithIndex.traverse((e, i) => e.elaborated(setName, i)).run.map(_._2)

object FrFlowExamples:
  /** A class's simple name as a Lean identifier: as it is when it is ASCII letters and digits starting with a letter;
    * else what of it is (or `Examples`) and a hash of the class's full name, so names that differ only in what is
    * dropped stay apart.
    */
  def identifier(simple: String, full: String): String =
    val kept = simple.filter(c => c.isLetterOrDigit && c < 128)
    if kept == simple && kept.headOption.exists(_.isLetter) then kept
    else (if kept.headOption.exists(_.isLetter) then kept else "Examples" + kept) +
      Integer.toHexString(full.hashCode).toUpperCase

  /** The examples of one model's sets, each set's in the order written; refused when two sets have one name, their
    * examples' theorems (`example_<set>_<i>`) would be one (two classes of one simple name in two packages).
    */
  def elaborated(sets: List[FrFlowExamples]): ValidatedNec[ElabError, List[Elaborated]] =
    val clashes = sets.groupBy(_.setName).toList.sortBy(_._1).collect { case (n, xs) if xs.size > 1 =>
      ElabError(Site.Example(n), Fault.ExampleSetsClash(n, xs.map(_.getClass.getName).sorted))
    }
    NonEmptyChain.fromSeq(clashes).fold(sets.traverse(_.elaborated).map(_.flatten))(Validated.invalid)

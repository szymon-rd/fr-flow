package frflow.dsl.kb

import cats.data.ValidatedNec
import frflow.core.code.Attachment
import frflow.core.Elaborated
import frflow.core.example.{Gen, Generator}
import frflow.core.name.{KbName, SymbolName}
import frflow.dsl.build.{Deferred, ElabError}
import frflow.dsl.node.Node
import frflow.dsl.term.LeanType

/** The nodes as the model writes them, what gives each Definition its meaning, and the generators given for the
  * tests.
  */
final case class FrModel(name: KbName, nodes: List[Node], code: List[(SymbolName, Deferred[Attachment])],
    generators: List[Generator[?]]):
  /** Elaborated once per value (a `lazy val`: the FrModel is immutable), for every check and run of it. */
  lazy val elaborated: ValidatedNec[ElabError, Elaborated] = Elaborate(this)

  def withGenerator[T](g: Gen[T])(using t: LeanType[T]): FrModel =
    copy(generators = generators :+ Generator(t.ty, g))
  private[dsl] def attach(d: SymbolName, a: Deferred[Attachment]): FrModel =
    copy(code = code.filterNot(_._1 == d) :+ (d -> a))

object FrModel:
  def apply(name: String)(nodes: Node*): FrModel = FrModel(KbName(name), nodes.toList, Nil, Nil)

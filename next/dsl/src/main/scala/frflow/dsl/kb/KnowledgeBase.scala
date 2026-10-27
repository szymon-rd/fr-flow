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
final case class KnowledgeBase(name: KbName, nodes: List[Node],
    meanings: List[(SymbolName, Deferred[Attachment])], generators: List[Generator[?]]):
  /** Elaborated once per value (a `lazy val`: the knowledge base is immutable), for every check and run of it. */
  lazy val elaborated: ValidatedNec[ElabError, Elaborated] = Elaborate(this)

  def generating[T](g: Gen[T])(using t: LeanType[T]): KnowledgeBase =
    copy(generators = generators :+ Generator(t.ty, g))
  private[dsl] def attach(d: SymbolName, a: Deferred[Attachment]): KnowledgeBase =
    copy(meanings = meanings.filterNot(_._1 == d) :+ (d -> a))

object KnowledgeBase:
  def apply(name: String)(nodes: Node*): KnowledgeBase = KnowledgeBase(KbName(name), nodes.toList, Nil, Nil)

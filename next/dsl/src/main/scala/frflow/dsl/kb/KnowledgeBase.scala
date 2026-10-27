package frflow.dsl.kb

import cats.data.ValidatedNec
import frflow.core.code.Attachment
import frflow.core.Elaborated
import frflow.core.example.{Gen, Generator}
import frflow.core.name.{KbName, RelPath, SymbolName}
import frflow.dsl.build.{Deferred, ElabError, Source}
import frflow.dsl.node.{Node, Spans}
import frflow.dsl.term.LeanType

/** The nodes as the model writes them, what gives each Definition its meaning, the generators given for the tests,
  * and the file it is assembled in (`KnowledgeBase("Rooms")(…)`, made relative as a node's is).
  */
final case class KnowledgeBase(name: KbName, nodes: List[Node],
    meanings: List[(SymbolName, Deferred[Attachment])], generators: List[Generator[?]], writtenIn: Option[RelPath]):
  /** Elaborated once per value (a `lazy val`: the knowledge base is immutable), for every check and run of it. */
  lazy val elaborated: ValidatedNec[ElabError, Elaborated] = Elaborate(this)

  def generating[T](g: Gen[T])(using t: LeanType[T]): KnowledgeBase =
    copy(generators = generators :+ Generator(t.ty, g))
  private[dsl] def attach(d: SymbolName, a: Deferred[Attachment]): KnowledgeBase =
    copy(meanings = meanings.filterNot(_._1 == d) :+ (d -> a))

object KnowledgeBase:
  inline def apply(name: String)(nodes: Node*): KnowledgeBase =
    KnowledgeBase(KbName(name), nodes.toList, Nil, Nil, Some(Spans.relative(Source.file)))

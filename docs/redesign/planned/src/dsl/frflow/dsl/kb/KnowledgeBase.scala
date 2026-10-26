package frflow.dsl.kb

import cats.data.ValidatedNec
import frflow.core.code.Attachment
import frflow.core.Elaborated
import frflow.core.example.{Gen, Generator}
import frflow.core.name.{KbName, NodeId}
import frflow.dsl.build.{Deferred, ElabError}
import frflow.dsl.node.Node
import frflow.dsl.term.LeanType

/** The nodes as the model writes them, the code attached to operations, and the generators given for the tests. */
final case class KnowledgeBase(name: KbName, nodes: List[Node[?, ?]], code: List[(NodeId, Deferred[Attachment])],
    generators: List[Generator[?]]):
  /** Elaborated once per value (a `lazy val`: the knowledge base is immutable), for every run and service of it. */
  lazy val elaborated: ValidatedNec[ElabError, Elaborated] = Elaborate(this)

  def generating[T](g: Gen[T])(using t: LeanType[T]): KnowledgeBase =
    copy(generators = generators :+ Generator(t.ty, g))
  private[dsl] def attach(id: NodeId, a: Deferred[Attachment]): KnowledgeBase =
    copy(code = code.filterNot(_._1 == id) :+ (id -> a))

object KnowledgeBase:
  def apply(name: String)(nodes: Node[?, ?]*): KnowledgeBase = KnowledgeBase(KbName(name), nodes.toList, Nil, Nil)

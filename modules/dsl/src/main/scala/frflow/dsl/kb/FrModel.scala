package frflow.dsl.kb

import cats.data.ValidatedNec
import frflow.core.code.Attachment
import frflow.core.Elaborated
import frflow.core.example.{Gen, Generator}
import frflow.core.name.{KbName, RelPath, SymbolName}
import frflow.dsl.build.{Deferred, ElabError, Source}
import frflow.dsl.node.{Node, Spans}
import frflow.dsl.term.LeanType
import frflow.dsl.vocab.Definition

/** The nodes as the model writes them, what gives each Definition its meaning, the plain Scala given operations on
  * a state (`defineOperations(ops*)(…)`), the generators given for the tests, the file it is assembled in
  * (`FrModel("Rooms")(…)`, made relative as a node's is), and the Definitions that are members of a structure
  * given a class: their code is theirs whether or not a statement mentions them.
  */
final case class FrModel(name: KbName, nodes: List[Node], meanings: List[(SymbolName, Deferred[Attachment])],
    operations: List[Operations], generators: List[Generator[?]], writtenIn: Option[RelPath],
    members: Set[SymbolName] = Set.empty, holds: Map[SymbolName, Set[SymbolName]] = Map.empty):
  /** Elaborated once per value (a `lazy val`: the FrModel is immutable), for every check and run of it. */
  lazy val elaborated: ValidatedNec[ElabError, Elaborated] = Elaborate(this)
  /** The words the model fixes: those it gives a meaning, and those its code calls (`Elaborate.fixed`). */
  lazy val fixed: Set[SymbolName] = Elaborate.fixed(this)

  def withGenerator[T](g: Gen[T])(using t: LeanType[T]): FrModel =
    copy(generators = generators :+ Generator(t.ty, g))
  private[dsl] def attach(d: SymbolName, a: Deferred[Attachment]): FrModel =
    copy(meanings = meanings.filterNot(_._1 == d) :+ (d -> a))
  /** The same of a structure's member: its code is its meaning whether or not a statement mentions it. */
  private[dsl] def attachMember(d: SymbolName, a: Deferred[Attachment]): FrModel =
    attach(d, a).copy(members = members + d)
  /** The same, the structure `holder` holding the structures of the words `parts` (`Stating.holds`). */
  private[dsl] def holding(holder: SymbolName, parts: List[SymbolName]): FrModel =
    copy(holds = parts.foldLeft(holds)((all, p) => all.updated(p, all.getOrElse(p, Set.empty) + holder)))
  /** The same model with these Definitions listed too: a word given a meaning here takes it in place of one it
    * had.
    */
  def defining(definitions: (Definition[?] | Definitions)*): FrModel = definitions.foldLeft(this) {
    case (kb, d: Defined[?])  => kb.taking(d.gives)
    case (kb, d: Definitions) => kb.taking(d.gives)
    case (kb, _)              => kb
  }

  /** The same, with what a Definition listed in it gives: each word's meaning, once. */
  private def taking(given_ : FrModel): FrModel =
    given_.meanings.foldLeft(this)((kb, m) => kb.attach(m._1, m._2))
      .copy(operations = operations ++ given_.operations, members = members ++ given_.members,
        holds = given_.holds.foldLeft(holds)((all, h) => all.updated(h._1, all.getOrElse(h._1, Set.empty) ++ h._2)))
  private[dsl] def implement(o: Operations): FrModel = copy(operations = operations :+ o)

object FrModel:
  /** What a FrModel is made of: its nodes, and the Definitions of its words (`granted.define { … }`,
    * `defineOperations(inRoom, add)(…)(…)`). A Definition declared and defined at once (`define { … }`) needs no
    * listing: a statement or code that mentions it brings it.
    */
  type Part = Node | Definition[?] | Definitions

  inline def apply(name: String)(parts: Part*): FrModel =
    of(FrModel(KbName(name), Nil, Nil, Nil, Nil, Some(Spans.relative(Source.file))), parts.toList)

  /** A model of nothing, for what a Definition gives one (`Defined.gives`). */
  private[kb] def part: FrModel = FrModel(KbName(""), Nil, Nil, Nil, Nil, None)

  private def of(empty: FrModel, parts: List[Part]): FrModel =
    empty.copy(nodes = parts.collect { case n: Node => n }).defining(parts.collect {
      case d: Definition[?] => d
      case d: Definitions   => d
    }*)

package frflow.dsl.kb

import cats.data.ValidatedNec
import frflow.core.code.Attachment
import frflow.core.Elaborated
import frflow.core.example.{Gen, Generator}
import frflow.core.name.{KbName, RelPath, SymbolName}
import frflow.dsl.build.{Deferred, ElabError, Source}
import frflow.dsl.node.{Node, Spans}
import frflow.dsl.term.RocqType
import frflow.dsl.vocab.{Definition, Held}

/** The nodes as the model writes them, what gives each Definition its meaning, the generators given for the tests,
  * the file it is assembled in (`FrModel("Rooms")(…)`, made relative as a node's is), and the Definitions that are
  * members of a structure given a class: their code is theirs whether or not a statement mentions them.
  */
final case class FrModel(name: KbName, nodes: List[Node], meanings: List[(SymbolName, Deferred[Attachment])],
    generators: List[Generator[?]], writtenIn: Option[RelPath], members: Set[SymbolName] = Set.empty,
    holdings: List[FrModel.Holding] = Nil):
  /** Which structures hold each structure, by their words (`Stating.held`). */
  def held: Held = Held(holdings.groupMap(_.part)(h => h.holder -> h.via).view.mapValues(_.toMap).toMap)
  /** What each word of "what a structure holds" gives: the held structure's members' words (`CodeTable.held`). */
  def reached: Map[SymbolName, Set[SymbolName]] = holdings.map(h => h.word -> h.members.toSet).toMap
  /** Elaborated once per value (a `lazy val`: the FrModel is immutable), for every check and run of it. */
  lazy val elaborated: ValidatedNec[ElabError, Elaborated] = Elaborate(this)
  /** The words the model fixes: those it gives a meaning, and those its code calls (`Elaborate.fixed`). */
  lazy val fixed: Set[SymbolName] = Elaborate.fixed(this)

  def withGenerator[T](g: Gen[T])(using t: RocqType[T]): FrModel =
    copy(generators = generators :+ Generator(t.ty, g))
  private[dsl] def attach(d: SymbolName, a: Deferred[Attachment]): FrModel =
    copy(meanings = meanings.filterNot(_._1 == d) :+ (d -> a))
  /** The same of a structure's member: its code is its meaning whether or not a statement mentions it. */
  private[dsl] def attachMember(d: SymbolName, a: Deferred[Attachment]): FrModel =
    attach(d, a).copy(members = members + d)
  /** The same, with what a structure's class holds. */
  private[dsl] def holding(held: List[FrModel.Holding]): FrModel = copy(holdings = (holdings ++ held).distinct)
  /** The same model with these Definitions listed too: a word given a meaning here takes it in place of one it
    * had.
    */
  def defining(definitions: Definition[?]*): FrModel = definitions.foldLeft(this) {
    case (kb, d: Defined[?]) => kb.taking(d.gives)
    case (kb, _)             => kb
  }

  /** The same, with what a Definition listed in it gives: each word's meaning, once. */
  private def taking(given_ : FrModel): FrModel =
    given_.meanings.foldLeft(this)((kb, m) => kb.attach(m._1, m._2))
      .copy(members = members ++ given_.members, holdings = (holdings ++ given_.holdings).distinct)

object FrModel:
  /** A structure held by another's class: the holder's word, the held one's, the word that is what the holder
    * holds as it (`via`, by its name `word`), and the held structure's members' words.
    */
  final case class Holding(holder: SymbolName, part: SymbolName, word: SymbolName, members: List[SymbolName])(
      val via: Definition[?])

  /** What a FrModel is made of: its nodes, and the Definitions of its words (`granted.define { … }`). A Definition
    * declared and defined at once (`define { … }`) needs no listing: a statement or code that mentions it brings it.
    */
  type Part = Node | Definition[?]

  inline def apply(name: String)(parts: Part*): FrModel =
    of(FrModel(KbName(name), Nil, Nil, Nil, Some(Spans.relative(Source.file))), parts.toList)

  /** A model of nothing, for what a Definition gives one (`Defined.gives`). */
  private[kb] def part: FrModel = FrModel(KbName(""), Nil, Nil, Nil, None)

  private def of(empty: FrModel, parts: List[Part]): FrModel =
    empty.copy(nodes = parts.collect { case n: Node => n }).defining(parts.collect { case d: Definition[?] => d }*)

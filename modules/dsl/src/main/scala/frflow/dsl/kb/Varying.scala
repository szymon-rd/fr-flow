package frflow.dsl.kb

import cats.data.{NonEmptyChain, Validated, ValidatedNec}
import frflow.core.name.{DefName, NodeId, SymbolName}
import frflow.core.spec.Range
import frflow.core.vocab.ValueKind
import frflow.dsl.build.{Declarations, ElabError, Fault, Site}
import frflow.dsl.node.Node
import frflow.dsl.run.Worlds
import frflow.dsl.vocab.Stating

/** Which Declarations change with the World (owner §43), read off the FrModel's statements: those a statement reads
  * beside what changes with it (a model's state, a program's run, a define reading state, `isConstant`, or another
  * such Declaration), until no statement adds one. Every Declaration may change with the World; one no statement
  * reads so is the same in each world whatever it is, so Lean is given it as a value, not a function of the world.
  * A rule (`always`) holds of values, in no world: a Declaration it reads must be one that does not change with the
  * World (owner §45 C, `Fault.RuleOverChanging` otherwise). Each statement is read once open for this
  * (`Stating.probing`), then elaborated over the world it holds in.
  */
object Varying:
  /** What one statement read open tells: its Declarations, whether it reads the world, whether it is a rule. */
  private final case class Read(node: NodeId, declarations: Set[SymbolName], world: Boolean, rule: Boolean)

  def of(nodes: List[Node], fixed: Set[SymbolName]): ValidatedNec[ElabError, Set[SymbolName]] =
    val read = nodes.flatMap(n => n.statement(Stating.probing(fixed)).run.toOption.flatMap((ds, s) =>
      s.said.map(f => Read(n.head.id, mentioned(ds), Worlds.in(f.value), s.range.exists(_ != Range.Possible)))))
    val statements = read.filterNot(_.rule)
    val varying = closure(statements.filter(_.world).flatMap(_.declarations).toSet, statements.map(_.declarations))
    val over = read.filter(_.rule).flatMap(r => (r.declarations & varying).toList.sortBy(_.value).map(d =>
      ElabError(Site.Node(r.node), Fault.RuleOverChanging(d.value, r.node.value, beside(statements, d)))))
    NonEmptyChain.fromSeq(over).fold(Validated.validNec(varying))(Validated.invalid)

  /** Every Declaration a statement mentions beside one that changes, added until none is. */
  private def closure(varying: Set[SymbolName], statements: List[Set[SymbolName]]): Set[SymbolName] =
    val more = varying ++ statements.filter(_.exists(varying)).flatten
    if more == varying then varying else closure(more, statements)

  /** A statement reading `d` beside the World. */
  private def beside(statements: List[Read], d: SymbolName): String =
    statements.find(r => r.world && r.declarations(d)).orElse(statements.find(_.declarations(d)))
      .fold("a statement")(_.node.value)

  /** The Declarations a statement mentions, those of the defines it calls among them (its rule's, a `stated`
    * define's), through the defines they call.
    */
  private def mentioned(ds: Declarations): Set[SymbolName] =
    within(List(ds), Set.empty).flatMap(_.symbols.collect {
      case (n, ss) if ss.exists(_.kind == ValueKind.Declaration) => n }).toSet

  /** `ds` and what every define they declare declares, each define read once. */
  private def within(ds: List[Declarations], seen: Set[DefName]): List[Declarations] =
    val next = ds.flatMap(_.defines.toList).filterNot((n, _) => seen(n))
    val more = next.flatMap(_._2).flatMap(_.run.toOption.map(_._1))
    if next.isEmpty then ds else ds ++ within(more, seen ++ next.map(_._1))

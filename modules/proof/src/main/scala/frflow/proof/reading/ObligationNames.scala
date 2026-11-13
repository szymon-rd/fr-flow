package frflow.proof.reading

import frflow.core.name.{ProverNames, NodeId}
import frflow.proof.prover.lower.LowerObligation
import frflow.proof.obligation.{ObligationName, TryKind}

/** An obligation, and a try, written as the name of its theorem (`LowerObligation.name`: `complete`, `cover_add`,
  * `needed_Grant`, `restates_2_Visibility`, `satisfiable_1_Book`), and read back from it.
  */
object ObligationNames:
  def text(o: ObligationName): String = LowerObligation.name(o).text
  def text(k: TryKind): String = text(ObligationName.Tried(k))

  private val fixed: Map[String, ObligationName] = List(ObligationName.Complete, ObligationName.Feasible,
    ObligationName.Impl, ObligationName.RootImpl, ObligationName.Outside).map(o => text(o) -> o).toMap
  private val fixedTries: Map[String, TryKind] =
    List(TryKind.Vacuous, TryKind.Restates, TryKind.Clash, TryKind.Unsat, TryKind.Idle)
      .map(k => text(k) -> k).toMap

  def tryKind(s: String): Option[TryKind] = fixedTries.get(s)
    .orElse(after("needed_", s).map(p => TryKind.Needed(NodeId(p))))
    .orElse(after("restates_", s).flatMap(numbered).map((i, p) => TryKind.RestatesConjunct(NodeId(p), i)))

  def read(s: String): Option[ObligationName] = fixed.get(s).orElse(tryKind(s).map(ObligationName.Tried(_)))
    .orElse(after(ProverNames.Made, s).map(ObligationName.Made(_)))
    .orElse(after("consistent_", s).flatMap(_.toIntOption).map(ObligationName.Consistent(_)))
    .orElse(after("inhabited_", s).map(n => ObligationName.Inhabited(NodeId(n))))
    .orElse(after("satisfiable_", s).flatMap(numbered).map((i, n) => ObligationName.Satisfiable(NodeId(n), i - 1)))
    .orElse(after("example_", s).flatMap(s => Option.when(s.endsWith("_opposite"))(s.stripSuffix("_opposite")))
      .flatMap(ofSet).map(ObligationName.ExampleOpposite(_, _)))
    .orElse(after("example_", s).flatMap(ofSet).map(ObligationName.Example(_, _)))

  private def after(prefix: String, s: String): Option[String] =
    Option.when(s.startsWith(prefix))(s.drop(prefix.length))

  /** `<set>_<i>`, the set a Rocq identifier. */
  private def ofSet(s: String): Option[(String, Int)] = s.lastIndexOf('_') match
    case -1 => None
    case k  => Option.when(s.take(k).nonEmpty && s.take(k).forall(_.isLetterOrDigit))(s.take(k))
        .flatMap(of => s.drop(k + 1).toIntOption.map(of -> _))

  /** `<i>_<rest>`. */
  private def numbered(s: String): Option[(Int, String)] = s.split("_", 2) match
    case Array(i, rest) => i.toIntOption.map(_ -> rest)
    case _              => None

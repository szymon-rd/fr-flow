package frflow.wire.check

import frflow.core.name.NodeId
import frflow.proof.obligation.{ObligationName, TryKind}
import io.circe.{Codec, Decoder, Encoder}

/** An obligation, and a try, written as the name of its theorem in Lean (`complete`, `cover_add`, `needed_Grant`,
  * `restates_2_Visibility`, `satisfiable_1_Book`), and read back from it.
  */
object ObligationNames:
  def text(o: ObligationName): String = o match
    case ObligationName.Complete          => "complete"
    case ObligationName.Feasible          => "feasible"
    case ObligationName.Impl              => "impl"
    case ObligationName.RootImpl          => "root_impl"
    case ObligationName.Cover(op)         => s"cover_$op"
    case ObligationName.Made(m)           => s"made_$m"
    case ObligationName.Commute(i)        => s"commute_$i"
    case ObligationName.Consistent(i)     => s"consistent_$i"
    case ObligationName.Start(n)          => s"start_${n.value}"
    case ObligationName.Inhabited(n)      => s"inhabited_${n.value}"
    case ObligationName.Satisfiable(n, i) => s"satisfiable_${i + 1}_${n.value}"
    case ObligationName.Example(i)        => s"example_$i"
    case ObligationName.Tried(k)          => text(k)

  def text(k: TryKind): String = k match
    case TryKind.Needed(p)              => s"needed_${p.value}"
    case TryKind.Vacuous                => "vacuous"
    case TryKind.Restates               => "restates"
    case TryKind.Clash                  => "clash"
    case TryKind.Unsat                  => "unsat"
    case TryKind.Idle                   => "idle"
    case TryKind.RestatesConjunct(p, i) => s"restates_${i}_${p.value}"

  private val fixed: Map[String, ObligationName] = List(ObligationName.Complete, ObligationName.Feasible,
    ObligationName.Impl, ObligationName.RootImpl).map(o => text(o) -> o).toMap
  private val fixedTries: Map[String, TryKind] =
    List(TryKind.Vacuous, TryKind.Restates, TryKind.Clash, TryKind.Unsat, TryKind.Idle).map(k => text(k) -> k).toMap

  def tryKind(s: String): Option[TryKind] = fixedTries.get(s)
    .orElse(after("needed_", s).map(p => TryKind.Needed(NodeId(p))))
    .orElse(after("restates_", s).flatMap(numbered).map((i, p) => TryKind.RestatesConjunct(NodeId(p), i)))

  def obligation(s: String): Option[ObligationName] = fixed.get(s).orElse(tryKind(s).map(ObligationName.Tried(_)))
    .orElse(after("cover_", s).map(ObligationName.Cover(_)))
    .orElse(after("made_", s).map(ObligationName.Made(_)))
    .orElse(after("commute_", s).flatMap(_.toIntOption).map(ObligationName.Commute(_)))
    .orElse(after("consistent_", s).flatMap(_.toIntOption).map(ObligationName.Consistent(_)))
    .orElse(after("start_", s).map(n => ObligationName.Start(NodeId(n))))
    .orElse(after("inhabited_", s).map(n => ObligationName.Inhabited(NodeId(n))))
    .orElse(after("satisfiable_", s).flatMap(numbered).map((i, n) => ObligationName.Satisfiable(NodeId(n), i - 1)))
    .orElse(after("example_", s).flatMap(_.toIntOption).map(ObligationName.Example(_)))

  given Codec[ObligationName] = codec("obligation", obligation)(text)
  given Codec[TryKind] = codec("try", tryKind)(text)

  private def codec[A](what: String, read: String => Option[A])(write: A => String): Codec[A] =
    Codec.from(Decoder.decodeString.emap(s => read(s).toRight(s"no $what $s")), Encoder.encodeString.contramap(write))

  private def after(prefix: String, s: String): Option[String] =
    Option.when(s.startsWith(prefix))(s.drop(prefix.length))

  /** `<i>_<rest>`. */
  private def numbered(s: String): Option[(Int, String)] = s.split("_", 2) match
    case Array(i, rest) => i.toIntOption.map(_ -> rest)
    case _              => None

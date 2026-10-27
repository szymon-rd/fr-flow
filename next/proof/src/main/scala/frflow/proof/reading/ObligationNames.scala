package frflow.proof.reading

import frflow.core.name.NodeId
import frflow.proof.obligation.{ObligationName, TryKind}

/** An obligation's name read back from its theorem's (`lean.lower.LowerObligation.name` spells it). */
object ObligationNames:
  import ObligationName.*

  def read(s: String): Option[ObligationName] = fixed.get(s).orElse(numbered(s)).orElse(named(s))

  private val fixed: Map[String, ObligationName] = Map("complete" -> Complete, "feasible" -> Feasible,
    "impl" -> Impl, "root_impl" -> RootImpl, "vacuous" -> Tried(TryKind.Vacuous),
    "restates" -> Tried(TryKind.Restates), "clash" -> Tried(TryKind.Clash), "unsat" -> Tried(TryKind.Unsat),
    "idle" -> Tried(TryKind.Idle))

  private val Indexed = """([a-z]+)_(\d+)""".r
  private val IndexedNode = """([a-z]+)_(\d+)_(.+)""".r
  private val Of = """([a-z]+)_(.+)""".r

  private def numbered(s: String): Option[ObligationName] = s match
    case Indexed("commute", i)            => Some(Commute(i.toInt))
    case Indexed("consistent", i)         => Some(Consistent(i.toInt))
    case Indexed("example", i)            => Some(Example(i.toInt))
    case IndexedNode("satisfiable", i, n) => Some(Satisfiable(NodeId(n), i.toInt - 1))
    case IndexedNode("restates", i, n)    => Some(Tried(TryKind.RestatesConjunct(NodeId(n), i.toInt)))
    case _                                => None

  private def named(s: String): Option[ObligationName] = s match
    case Of("cover", op)    => Some(Cover(op))
    case Of("made", m)      => Some(Made(m))
    case Of("start", n)     => Some(Start(NodeId(n)))
    case Of("inhabited", n) => Some(Inhabited(NodeId(n)))
    case Of("needed", n)    => Some(Tried(TryKind.Needed(NodeId(n))))
    case _                  => None

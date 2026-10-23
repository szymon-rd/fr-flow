package frflow
package lean

import frflow.protocol.TryKind

/** The name of what Lean is asked about a node: an obligation, a try, an example evaluated. It is the
  * name of the theorem in the generated Lean (`lean`), and the name its result is recorded under.
  */
enum ObligationName:
  /** The parts of a node together make it. */
  case Complete
  /** Some world meets the parts: an authored `complete` does not rest on a contradiction. */
  case Feasible
  /** Every result of the proven code meets the contract. */
  case Impl
  /** What the service checks on every call follows from the post. */
  case Check
  /** The view of `invariant` lists all a result holds of it. */
  case Cover(invariant: String)
  /** Expectation `i` follows from the node. */
  case Expect(i: Int)
  /** A try (see `TryKind`). */
  case Tried(kind: TryKind)
  /** Example `i`, evaluated in Lean: of the contract, and of its proven code. */
  case Eval(i: Int)
  case EvalImpl(i: Int)
  /** Probe `j` (an input near the examples'), evaluated in Lean: of the contract, and of its proven code. */
  case Probe(j: Int)
  case ProbeImpl(j: Int)
  /** The root holds of the code. */
  case RootImpl

  /** The theorem's name in Lean. */
  def lean: String = this match
    case Complete    => "complete"
    case Feasible    => "feasible"
    case Impl        => "impl"
    case Check       => "check"
    case Cover(i)    => s"cover_$i"
    case Expect(i)   => s"expect_$i"
    case Tried(k)    => ObligationName.tryName(k)
    case Eval(i)     => s"eval_$i"
    case EvalImpl(i) => s"evalImpl_$i"
    case Probe(j)    => s"probe_$j"
    case ProbeImpl(j) => s"probeImpl_$j"
    case RootImpl    => "root_impl"

  override def toString: String = lean

  /** An example or a probe, evaluated in Lean: the translation's cross-check. */
  def isEvaluation: Boolean = this match
    case Eval(_) | EvalImpl(_) | Probe(_) | ProbeImpl(_) => true
    case _                                               => false

  def isProbe: Boolean = this match
    case Probe(_) | ProbeImpl(_) => true
    case _                       => false

  /** The same evaluation, of the proven code instead of the contract. */
  def ofCode: ObligationName = this match
    case Eval(i)  => EvalImpl(i)
    case Probe(j) => ProbeImpl(j)
    case other    => other

object ObligationName:
  private def tryName(k: TryKind): String = k match
    case TryKind.Needed(part)     => s"needed_$part"
    case TryKind.Vacuous          => "vacuous"
    case TryKind.Restates         => "restates"
    case TryKind.Clash            => "clash"
    case TryKind.Unsat            => "unsat"
    case TryKind.Idle             => "idle"
    case TryKind.VacuousExpect(i) => s"vacuous_expect_$i"

  private val fixed: Map[String, ObligationName] =
    (List(Complete, Feasible, Impl, Check, RootImpl) ++
      List(TryKind.Vacuous, TryKind.Restates, TryKind.Clash, TryKind.Unsat, TryKind.Idle).map(Tried(_))).map(o => o.lean -> o).toMap
  private val Indexed = """(expect|vacuous_expect|eval|evalImpl|probe|probeImpl)_(\d{1,9})""".r
  private val OfNode = """(cover|needed)_(.+)""".r

  /** The name a theorem or a recorded result has, read back. */
  def parse(s: String): Option[ObligationName] = fixed.get(s).orElse(s match
    case Indexed(kind, i) => Some(indexed(kind, i.toInt))
    case OfNode("cover", id) => Some(Cover(id))
    case OfNode(_, id)       => Some(Tried(TryKind.Needed(id)))
    case _                   => None)

  private def indexed(kind: String, i: Int): ObligationName = kind match
    case "expect"         => Expect(i)
    case "vacuous_expect" => Tried(TryKind.VacuousExpect(i))
    case "eval"           => Eval(i)
    case "evalImpl"       => EvalImpl(i)
    case "probe"          => Probe(i)
    case _                => ProbeImpl(i)

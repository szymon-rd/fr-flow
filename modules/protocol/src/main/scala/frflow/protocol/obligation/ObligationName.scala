package frflow.protocol
package obligation

import io.circe.{Codec, Decoder, Encoder}

/** What Lean is asked about a node; `lean` names its theorem, and the result recorded. */
enum ObligationName:
  case Complete, Feasible, Impl, Check
  case Cover(invariant: String)
  case Expect(i: Int)
  case Tried(kind: TryKind)
  /** Example `i` (probe `j`: an input near the examples'), of the contract and of its proven code. */
  case Eval(i: Int)
  case EvalImpl(i: Int)
  case Probe(j: Int)
  case ProbeImpl(j: Int)
  case RootImpl
  /** The branches of the `i`-th parallel step of a node's proven code commute. */
  case Commute(i: Int)

  def lean: String = this match
    case Complete     => "complete"
    case Feasible     => "feasible"
    case Impl         => "impl"
    case Check        => "check"
    case Cover(i)     => s"cover_$i"
    case Expect(i)    => s"expect_$i"
    case Tried(k)     => ObligationName.tryName(k)
    case Eval(i)      => s"eval_$i"
    case EvalImpl(i)  => s"evalImpl_$i"
    case Probe(j)     => s"probe_$j"
    case ProbeImpl(j) => s"probeImpl_$j"
    case RootImpl     => "root_impl"
    case Commute(i)   => s"commute_$i"

  override def toString: String = lean
  def isProbe: Boolean = PartialFunction.cond(this) { case Probe(_) | ProbeImpl(_) => true }
  /** An example or a probe, evaluated in Lean: the translation's cross-check. */
  def isEvaluation: Boolean = isProbe || PartialFunction.cond(this) { case Eval(_) | EvalImpl(_) => true }

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
    case TryKind.RestatesConjunct(p, i) => s"restates_${i}_$p"

  private val fixed: Map[String, ObligationName] =
    (List(Complete, Feasible, Impl, Check, RootImpl) ++
      List(TryKind.Vacuous, TryKind.Restates, TryKind.Clash, TryKind.Unsat, TryKind.Idle).map(Tried(_))).map(o => o.lean -> o).toMap
  private val indexed: Map[String, Int => ObligationName] = Map("expect" -> Expect.apply, "eval" -> Eval.apply,
    "vacuous_expect" -> (i => Tried(TryKind.VacuousExpect(i))), "evalImpl" -> EvalImpl.apply, "probe" -> Probe.apply, "probeImpl" -> ProbeImpl.apply,
    "commute" -> Commute.apply)
  private val Indexed = s"(${indexed.keys.mkString("|")})_(\\d{1,9})".r
  private val OfNode = """(cover|needed)_(.+)""".r
  private val Conjunct = """restates_(\d{1,9})_(.+)""".r

  def parse(s: String): Option[ObligationName] = fixed.get(s).orElse(s match
    case Indexed(kind, i)    => indexed.get(kind).map(_(i.toInt))
    case Conjunct(i, id)     => Some(Tried(TryKind.RestatesConjunct(id, i.toInt)))
    case OfNode("cover", id) => Some(Cover(id))
    case OfNode(_, id)       => Some(Tried(TryKind.Needed(id)))
    case _                   => None)

  given Codec[ObligationName] = Codec.from(
    Decoder.decodeString.emap(s => parse(s).toRight(s"unknown obligation $s")), Encoder.encodeString.contramap(_.lean))

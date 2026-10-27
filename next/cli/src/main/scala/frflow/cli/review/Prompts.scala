package frflow.cli.review

import cats.effect.IO
import frflow.cli.term.{Style, Terminal}
import frflow.core.name.NodeId

/** What the review asks on a terminal: a key, a reason, the decisions below to revisit. Each is none at the end of
  * the input.
  */
final class Prompts(term: Terminal, st: Style):
  /** Asked again until the answer is one of `keys` (its first letter counts). */
  def choose(prompt: String, keys: Set[String]): IO[Option[String]] = term.read(prompt).flatMap {
    case None    => IO.pure(None)
    case Some(a) =>
      val k = a.trim.toLowerCase.take(1)
      if keys(k) then IO.pure(Some(k))
      else term.out(st.dim(s"one of: ${keys.toList.sorted.filter(_.nonEmpty).mkString(" ")}")) >> choose(prompt, keys)
  }

  def reason(prompt: String): IO[Option[String]] = term.read(prompt).map(_.map(_.trim).filter(_.nonEmpty))

  /** Asked again until each name is one of `candidates`; none named when there are none. */
  def revisit(of: NodeId, candidates: List[NodeId]): IO[Option[List[NodeId]]] =
    if candidates.isEmpty then IO.pure(Some(Nil))
    else term.read(s"Revisit any decision below that this may affect (${candidates.mkString(" ")}; Enter for none)? ")
      .flatMap {
        case None    => IO.pure(None)
        case Some(a) =>
          val named = a.split("[\\s,]+").filter(_.nonEmpty).map(NodeId(_)).toList.distinct
          val other = named.filterNot(candidates.contains)
          if other.isEmpty then IO.pure(Some(named))
          else term.out(st.red(s"not a decision below $of: ${other.mkString(" ")}")) >> revisit(of, candidates)
      }

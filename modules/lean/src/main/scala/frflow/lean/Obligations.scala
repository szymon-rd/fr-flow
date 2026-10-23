package frflow
package lean

import frflow.protocol.TryKind
import ObligationName.*

/** A statement Lean is asked to prove (or, for a try, that it is asked whether it can prove). */
final case class Obligation(name: ObligationName, statement: String, description: String)

/** A try: a statement Lean is asked whether it can prove, cheaply; if it does, `means` what is wrong. */
final case class Try(kind: TryKind, obligation: Obligation, means: String)

/** What Lean is asked of each node: its obligations, each proven by `frflow_auto` or authored, and its tries.
  *
  * @param authored (node, obligation) proven by a theorem of that name in `Proofs/<KB>/<Node>.lean`
  */
final class Obligations(kb: KnowledgeBase, refinement: Refinement, coverage: Coverage, authored: Set[(String, ObligationName)]):
  import refinement.*
  import refinement.vocabulary.*

  /** Whether the proof file of `n` proves its obligation `name`. */
  def isAuthored(n: Node[?], name: ObligationName): Boolean = authored((n.id, name))

  /** The obligations of a node: its split, its code, its cheap check, its kept invariants' coverage,
    * the expectations; `feasible` with an authored split.
    */
  def obligations(n: Node[?]): List[Obligation] =
    complete(n).toList ++ feasible(n) ++ implementation(n) ++ check(n) ++ covers(n) ++ expects(n)

  def obligation(n: Node[?], name: ObligationName): Option[Obligation] = obligations(n).find(_.name == name)

  /** Obligations proven in the Checks file: all but `complete` and `impl`. */
  def extraObligations(n: Node[?]): List[Obligation] = obligations(n).filterNot(o => o.name == Complete || o.name == Impl)

  private def complete(n: Node[?]): Option[Obligation] = splitParts(n).map { ps =>
    Obligation(Complete, stated(splitOpens(n, ps), hyps(ps).map(_._1), claim(n)._1), s"The parts of ${n.id} (${ps.map(_.id).mkString(", ")}) together make it.")
  }

  // A proof the agent wrote may rest on a contradiction automation did not find: then something
  // must meet the parts, unless they are witnessed (see `witnessed`). A proof file that proves it
  // anyway keeps its statement.
  private def feasible(n: Node[?]): Option[Obligation] =
    splitParts(n).filter(_ => isAuthored(n, Complete) && (!witnessed(n) || isAuthored(n, Feasible))).map { ps =>
      val b = binders(splitOpens(n, ps))
      Obligation(Feasible, s"${if b.isEmpty then "" else s"∃ $b, "}${hyps(ps).map(_._1._2).mkString(" ∧ ")}",
        s"Some world meets the parts of ${n.id}: its authored proof does not rest on a contradiction.")
    }

  private def implementation(n: Node[?]): Option[Obligation] =
    for { d <- provenImpl(n); op <- n.op } yield
      val (concl, opens) = ofCode(n, d, op.name)
      val hs = hyps(calls(n))
      Obligation(Impl, stated(opens, hs.map(_._1), concl),
        s"Every result of ${d.name} meets ${n.id}${if hs.isEmpty then "" else s", given what ${calls(n).map(_.id).mkString(", ")} promise"}.")

  private def check(n: Node[?]): Option[Obligation] =
    for { l <- n.local; post <- n.post if formal(n) } yield
      val (vars, xs) = LeanText.call(post.params.map(_._2))
      val (p, po) = app(qualified(n, "post"), ctx(post))
      val (c, cc) = app(qualified(n, "runCheck"), ctx(l))
      Obligation(Check, stated(po ++ cc, Nil, s"∀ $vars, $p $xs → $c $xs"),
        s"What service checks of ${n.id} on every call follows from its post: it refuses nothing the contract allows.")

  private def covers(n: Node[?]): List[Obligation] = formalKeeps(n).flatMap { (inv, _) =>
    coverage.coverage(n, inv).toOption.flatten.map((stmt, o) => Obligation(Cover(inv.id), stated(o, Nil, stmt),
      s"The view of ${inv.id} lists all the result holds of it, each with the caller."))
  }

  private def expected(n: Node[?], i: Int, l: Lifted[?]): (String, Ctx) = app(qualified(n, s"expected_$i"), ctx(l))

  private def expects(n: Node[?]): List[Obligation] =
    if !formal(n) then Nil
    else n.expected.zipWithIndex.map { case ((statement, l), i) =>
      val (c, co) = claim(n)
      val (e, eo) = expected(n, i, l)
      Obligation(Expect(i), stated(co ++ eo, List("h" -> c), e), statement)
    }

  private def tried(kind: TryKind, statement: String, description: String, means: String): Try =
    Try(kind, Obligation(Tried(kind), statement, description), means)

  /** The tries of a node: a part not needed (with one part: the node says nothing it adds, or says only
    * what its part says), parts that contradict each other, no world meeting the node, an expectation that
    * checks nothing, and, for the root, doing nothing meeting it.
    */
  def tries(n: Node[?]): List[Try] =
    val (c, co) = claim(n)
    val unsat = tried(TryKind.Unsat, stated(co, Nil, s"¬ $c"), s"No world meets ${n.id}.", s"${n.id} is contradictory: no world meets it")
    val vacuousExpects = n.expected.zipWithIndex.map { case ((_, l), i) =>
      val (e, eo) = expected(n, i, l)
      tried(TryKind.VacuousExpect(i), stated(eo, Nil, e), s"The expectation holds whatever ${n.id} says.",
        "the expectation holds whatever the node says: it checks nothing")
    }
    if !formal(n) then Nil
    else splitParts(n).toList.flatMap(splitTries(n, _)) ++ List(unsat) ++ vacuousExpects ++
      idle(n).map(o => Try(TryKind.Idle, o, s"doing nothing meets ${n.id}"))

  /** With one part: whether the node says nothing it adds, or only what it says. With several: whether
    * each is needed. And whether the parts contradict each other.
    */
  private def splitTries(n: Node[?], ps: List[Node[?]]): List[Try] =
    val o = splitOpens(n, ps)
    val hs = hyps(ps)
    val goal = claim(n)._1
    val needed = ps match
      case List(p) => List(
        tried(TryKind.Vacuous, stated(o, Nil, goal), s"${n.id} holds whatever ${p.id} says.", s"${n.id} holds whatever ${p.id} says: it says nothing its part adds"),
        // With `complete`, the node and its part are then equivalent: one says what the other does.
        tried(TryKind.Restates, stated(o, List(s"h_${n.id}" -> goal), claim(p)._1), s"${p.id} follows from ${n.id}.",
          s"${n.id} says what ${p.id} says: merge them, or say what ${n.id} adds"))
      case _ => ps.map(c => tried(TryKind.Needed(c.id), stated(o, hs.filterNot(_._1._1 == s"h_${c.id}").map(_._1), goal),
          s"${n.id} holds without ${c.id}.", s"${c.id} is not needed for ${n.id}"))
    needed :+ tried(TryKind.Clash, stated(o, hs.map(_._1), "False"), s"The parts of ${n.id} contradict each other.",
      s"the parts of ${n.id} contradict each other: no world meets them all")

  /** The operations of the root that doing nothing can stand for (see `LeanType.nothing`), each with it. */
  private def nothings(n: Node[?]): List[(String, String)] =
    claim(n)._2.params.filter(kb.isOp).flatMap(o => LeanType.nothing(paramType(o).getOrElse("")).map(o -> _))

  /** The root with every operation it mentions replaced by doing nothing, when one can be. */
  def idle(n: Node[?]): Option[Obligation] =
    if !kb.root.exists(_ eq n) || !formal(n) then None
    else
      val env: Env = nothings(n).map((o, v) => o -> (v, leaf(o).copy(params = Nil))).toMap
      Option.when(env.nonEmpty) {
        val (c, o) = claim(n, env)
        Obligation(Tried(TryKind.Idle), stated(o, Nil, c), s"${n.id} is met by doing nothing (${env.keys.toList.sorted.mkString(", ")}: returning nothing).")
      }

  /** What doing nothing is, in words, for the root's idle. */
  def idleWhat(n: Node[?]): String = nothings(n).map(_._1).mkString(", ") + " doing nothing"

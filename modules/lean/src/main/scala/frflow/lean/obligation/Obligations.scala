package frflow
package lean
package obligation

import frflow.protocol.{ObligationName, TryKind}
import ObligationName.*

/** What Lean is asked of each node: its obligations, proven by `frflow_auto` or `authored`, and its tries. */
final class Obligations(kb: KnowledgeBase, refinement: Refinement, coverage: Coverage, authored: Set[(String, ObligationName)]):
  import refinement.*
  import refinement.vocabulary.*
  def isAuthored(n: Node[?], name: ObligationName): Boolean = authored((n.id, name))
  def obligations(n: Node[?]): List[Obligation] =
    complete(n).toList ++ feasible(n) ++ implementation(n) ++ commutes(n) ++ check(n) ++ covers(n) ++ keptBy(n) ++
      initially(n) ++ expects(n)
  def obligation(n: Node[?], name: ObligationName): Option[Obligation] = obligations(n).find(_.name == name)
  def extraObligations(n: Node[?]): List[Obligation] = obligations(n).filterNot(o => o.name == Complete || o.name == Impl)

  private def complete(n: Node[?]): Option[Obligation] = splitParts(n).map { ps =>
    val of = provenImpl(n).filter(_ => ofCodeStep(n)).fold("")(d => s", run as ${d.name}")
    Obligation(Complete, stated(splitOpens(n, ps), partHyps(ps).map(_._1), stepClaim(n)._1),
      s"The parts of ${n.id} (${ps.map(_.id).mkString(", ")}) together make it$of.")
  }

  // An authored proof may rest on a contradiction automation missed: something must meet the parts, unless witnessed.
  private def feasible(n: Node[?]): Option[Obligation] =
    splitParts(n).filter(_ => isAuthored(n, Complete) && (!witnessed(n) || isAuthored(n, Feasible))).map { ps =>
      val b = binders(splitOpens(n, ps))
      Obligation(Feasible, s"${if b.isEmpty then "" else s"∃ $b, "}${partHyps(ps).map(_._1._2).mkString(" ∧ ")}",
        s"Some world meets the parts of ${n.id}: its authored proof does not rest on a contradiction.")
    }

  private def implementation(n: Node[?]): Option[Obligation] =
    // A step of code: what its parts make is its code meeting it, so `impl` is `complete`.
    if ofCodeStep(n) then complete(n).map(c =>
      c.copy(name = Impl, description = s"Every result of ${provenImpl(n).fold("")(_.name)} meets ${n.id}, given what its parts say."))
    else for { d <- provenImpl(n); op <- n.op } yield
      val (concl, opens) = ofCode(n, d, op.name)
      val hs = hyps(calls(n))
      Obligation(Impl, stated(opens, hs.map(_._1), concl),
        s"Every result of ${d.name} meets ${n.id}${if hs.isEmpty then "" else s", given what ${calls(n).map(_.id).mkString(", ")} promise"}.")

  /** Each parallel step of the proven code: its branches in either order give the same result and the same world, from
    * every world (with no call failing, where boundaries may fail: the faults are taken in the order calls come, so
    * which call fails depends on the order). Whole branches: what each order does step by step is not compared.
    */
  private def commutes(n: Node[?]): List[Obligation] =
    (for { _ <- provenImpl(n).toList; d <- kb.implementation(n).flatMap(_.flowDef).toList } yield d.lifted.commutes.zipWithIndex.map { (c, i) =>
      val err = n.failure.map(f => frflow.Types.walk(f.err).lean)
      val monad = err.fold("StateM World")(e => s"ExceptT $e (StateM World)")
      def run(lines: List[String]) =
        val body = lines.map(l => s"\n        $l").mkString
        err.fold(s"FrFlow.runOn ((do$body) : $monad ${c.result})")(e => s"FrFlow.runOnE (ε := $e) ((do$body) : $monad ${c.result})")
      val vars = (c.free.map((x, t) => s"($x : $t)") :+ "(w : World)").mkString(" ")
      val noFaults = if kb.faulty then List("w.faults = []") else Nil
      val concl = resolve(s"∀ $vars, ${(c.hyps ++ noFaults).map(_ + " → ").mkString}\n      ${run(c.first)} w =\n      ${run(c.second)} w")
      Obligation(Commute(i), stated(defCtx(d), Nil, concl),
        s"The branches of the ${c.what} (number ${i + 1}) in ${d.name} commute: either order gives the same result and leaves the same world.")
    }).flatten

  private def check(n: Node[?]): Option[Obligation] =
    for { l <- n.local; post <- n.post if formal(n) } yield
      val (vars, xs) = LeanText.call(post.params.map(_._2))
      val (p, po) = app(qualified(n, "post"), ctx(post))
      val (c, cc) = app(qualified(n, "runCheck"), ctx(l))
      Obligation(Check, stated(po ++ cc, Nil, s"∀ $vars, $p $xs → $c $xs"),
        s"What service checks of ${n.id} on every call follows from its post: it forbids nothing the contract allows.")

  /** An `always` claim is kept by each program writing what it is about: its proven code, run from a world where
    * everything that always holds does (and on inputs that hold their types' rules), leaves a state that holds the
    * claim's rule, given what the operations the code calls promise.
    */
  private def keptBy(n: Node[?]): List[Obligation] =
    for
      rule      <- n.holds.toList
      c         <- kb.writers(n)
      d         <- provenImpl(c).toList
      post      <- c.post.toList
      m         <- kb.models.filter(m => kb.worldRules(m).exists(_._1 eq n))
      (_, _, reach) <- kb.worldRules(m).find(_._1 eq n).toList
    yield
      val ts = post.params.map(_._2)
      val ins = ts.dropRight(3)
      val (vars, xs) = LeanText.call(ins :+ ts(ts.size - 2))
      val hs = ins.zipWithIndex.flatMap((t, i) => assumed(s"x$i", t)) ++ worldAssumed(s"x${ins.size}")
      val (run, co) = code(d)
      val promised = hyps(calls(c))
      val kept = ruleOf(rule, s"($run $xs).2.${m.model.field}", reach)
      val worldRules = Ctx.all(kb.models.flatMap(kb.worldRules).map(r => defCtx(r._2)))
      val opens = co ++ Ctx.all(promised.map(_._2)) ++ defCtx(rule) ++ worldRules
      val program = c.op.fold(d.name)(_.name)
      Obligation(KeptBy(program), stated(opens, promised.map(_._1), s"∀ $vars, ${hs.map(_ + " → ").mkString}$kept"),
        s"$program (${d.name}) keeps ${n.id} of what ${m.model.lean} holds after a run.")

  /** What a store holds when the system starts, as an assumption says, holds an `always` claim's rule about it. */
  private def initially(n: Node[?]): List[Obligation] =
    for
      rule  <- n.holds.toList
      m     <- n.always.flatMap(_.store).toList
      start <- n.premises.filter(_.fact.exists(_.store.exists(_ eq m))).flatMap(_.initially)
    yield
      val t = frflow.Types.walk(m.stateType).lean
      val (r, ro) = code(rule)
      val (i, io) = code(start)
      val by = n.premises.find(_.initially.exists(_ eq start)).fold("")(_.id)
      Obligation(Initially, stated(ro ++ io, Nil, s"∀ (s : $t), $i s → $r s"),
        s"What ${m.lean} holds when the system starts ($by) holds ${n.id}.")

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

  def tries(n: Node[?]): List[Try] =
    val (c, co) = claim(n)
    val unsat = tried(TryKind.Unsat, stated(co, Nil, s"¬ $c"), s"No world meets ${n.id}.", s"${n.id} is contradictory: no world meets it")
    val vacuousExpects = n.expected.zipWithIndex.map { case ((_, l), i) =>
      val (e, eo) = expected(n, i, l)
      tried(TryKind.VacuousExpect(i), stated(eo, Nil, e), s"The expectation holds whatever ${n.id} says.",
        "the expectation holds whatever the node says: it checks nothing")
    }
    if !formal(n) || n.isAlways then Nil
    else splitParts(n).toList.flatMap(splitTries(n, _)) ++ List(unsat) ++ vacuousExpects ++
      idle(n).map(o => Try(TryKind.Idle, o, s"doing nothing meets ${n.id}"))

  private def splitTries(n: Node[?], ps: List[Node[?]]): List[Try] =
    val o = splitOpens(n, ps)
    val hs = partHyps(ps)
    val goal = stepClaim(n)._1
    val needed = ps match
      case List(p) => List(
        tried(TryKind.Vacuous, stated(o, Nil, goal), s"${n.id} holds whatever ${p.id} says.", s"${n.id} holds whatever ${p.id} says: it says nothing its part adds"),
        // With `complete`, the node and its part are then equivalent: one says what the other does.
        tried(TryKind.Restates, stated(o, List(s"h_${n.id}" -> goal), stepClaim(p)._1), s"${p.id} follows from ${n.id}.",
          s"${n.id} says what ${p.id} says: merge them, or say what ${n.id} adds"))
      case _ => ps.map(c => tried(TryKind.Needed(c.id), stated(o, hs.filterNot(_._1._1 == s"h_${c.id}").map(_._1), goal),
          s"${n.id} holds without ${c.id}.", s"${c.id} is not needed for ${n.id}"))
    // A part Lean shows equivalent to one conjunct of its parent only says that conjunct again, in other words.
    val conjuncts = ps.flatMap(p => conjunctsOf(n).indices.map(_ + 1).map { i =>
      tried(TryKind.RestatesConjunct(p.id, i), stated(o, Nil, s"(${claim(p)._1} ↔ ${conjunct(n, i)._1})"),
        s"${p.id} says what conjunct $i of ${n.id} says.", s"${p.id} says what conjunct $i of ${n.id} says: fold it into ${n.id}, or say what ${p.id} adds")
    })
    needed ++ conjuncts :+ tried(TryKind.Clash, stated(o, hs.map(_._1), "False"), s"The parts of ${n.id} contradict each other.",
      s"the parts of ${n.id} contradict each other: no world meets them all")
  /** The operations the root's service performs, each replaced by "nothing". A word left open above (`leftOpenAbove`:
    * "a share in force") is not one of them: it is the vocabulary a lower refinement fixes, and the root must hold for
    * every meaning of it, so it stays open. */
  private def nothings(n: Node[?]): List[(String, String)] =
    stepClaim(n)._2.params.filter(o => kb.isOp(o) && !kb.onOp(o).exists(_.openAbove))
      .flatMap(o => LeanType.nothing(paramType(o).getOrElse("")).map(o -> _))

  def idle(n: Node[?]): Option[Obligation] =
    if !kb.isRoot(n) || !formal(n) then None
    else
      val env: Env = nothings(n).map((o, v) => o -> (v, leaf(o).copy(params = Nil))).toMap
      Option.when(env.nonEmpty) {
        val (c, o) = stepClaim(n, env)
        Obligation(Tried(TryKind.Idle), stated(o, Nil, c), s"${n.id} is met by doing nothing (${env.keys.toList.sorted.mkString(", ")}: returning nothing).")
      }
  def idleWhat(n: Node[?]): String = nothings(n).map(_._1).mkString(", ") + " doing nothing"

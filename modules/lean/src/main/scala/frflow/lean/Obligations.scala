package frflow
package lean

import frflow.protocol.{ObligationName, TryKind}
import ObligationName.*

final case class Obligation(name: ObligationName, statement: String, description: String)

/** A try, and `means`: what is wrong if Lean proves it. */
final case class Try(kind: TryKind, obligation: Obligation, means: String)

/** What Lean is asked of each node: its obligations, proven by `frflow_auto` or `authored`, and its tries. */
final class Obligations(kb: KnowledgeBase, refinement: Refinement, coverage: Coverage, authored: Set[(String, ObligationName)]):
  import refinement.*
  import refinement.vocabulary.*
  def isAuthored(n: Node[?], name: ObligationName): Boolean = authored((n.id, name))
  def obligations(n: Node[?]): List[Obligation] =
    complete(n).toList ++ feasible(n) ++ implementation(n) ++ check(n) ++ covers(n) ++ expects(n)
  def obligation(n: Node[?], name: ObligationName): Option[Obligation] = obligations(n).find(_.name == name)
  def extraObligations(n: Node[?]): List[Obligation] = obligations(n).filterNot(o => o.name == Complete || o.name == Impl)

  private def complete(n: Node[?]): Option[Obligation] = splitParts(n).map { ps =>
    Obligation(Complete, stated(splitOpens(n, ps), hyps(ps).map(_._1), claim(n)._1), s"The parts of ${n.id} (${ps.map(_.id).mkString(", ")}) together make it.")
  }

  // An authored proof may rest on a contradiction automation missed: something must meet the parts, unless witnessed.
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
    // A part Lean shows equivalent to one conjunct of its parent only says that conjunct again, in other words.
    val conjuncts = ps.flatMap(p => conjunctsOf(n).indices.map(_ + 1).map { i =>
      tried(TryKind.RestatesConjunct(p.id, i), stated(o, Nil, s"(${claim(p)._1} ↔ ${conjunct(n, i)._1})"),
        s"${p.id} says what conjunct $i of ${n.id} says.", s"${p.id} says what conjunct $i of ${n.id} says: fold it into ${n.id}, or say what ${p.id} adds")
    })
    needed ++ conjuncts :+ tried(TryKind.Clash, stated(o, hs.map(_._1), "False"), s"The parts of ${n.id} contradict each other.",
      s"the parts of ${n.id} contradict each other: no world meets them all")
  private def nothings(n: Node[?]): List[(String, String)] =
    claim(n)._2.params.filter(kb.isOp).flatMap(o => LeanType.nothing(paramType(o).getOrElse("")).map(o -> _))

  def idle(n: Node[?]): Option[Obligation] =
    if !kb.root.exists(_ eq n) || !formal(n) then None
    else
      val env: Env = nothings(n).map((o, v) => o -> (v, leaf(o).copy(params = Nil))).toMap
      Option.when(env.nonEmpty) {
        val (c, o) = claim(n, env)
        Obligation(Tried(TryKind.Idle), stated(o, Nil, c), s"${n.id} is met by doing nothing (${env.keys.toList.sorted.mkString(", ")}: returning nothing).")
      }
  def idleWhat(n: Node[?]): String = nothings(n).map(_._1).mkString(", ") + " doing nothing"

/** `cover_<invariant>`: a contract's view of an invariant lists every value of the rule's type its result holds. */
final class Coverage(kb: KnowledgeBase, refinement: Refinement):
  import refinement.*
  import refinement.vocabulary.*
  import LeanType.*
  private val typeDecls: Map[String, TypeDecl] = kb.types.map(t => t.name -> t).toMap

  /** `y` occurs in `x` of type `t`: None if `t` can never hold a `target`; Left if FrFlow cannot unfold `t`. */
  private def occurs(y: String, x: String, t: LeanType, target: LeanType, seen: Set[String] = Set.empty): Either[String, Option[String]] =
    val fresh = s"z${seen.size}_${x.count(_ == '.')}${x.length}'"
    def any(parts: List[Either[String, Option[String]]]): Either[String, Option[String]] =
      parts.collectFirst { case Left(w) => w }.toLeft {
        val ps = parts.collect { case Right(Some(p)) => p }
        Option.when(ps.nonEmpty)(ps.mkString("(", " ∨ ", ")"))
      }
    if t == target then Right(Some(s"$y = $x"))
    else t match
      case ListOf(e)   => occurs(y, fresh, e, target, seen).map(_.map(b => s"(∃ $fresh ∈ $x, $b)"))
      case OptionOf(e) => occurs(y, fresh, e, target, seen).map(_.map(b => s"(∃ $fresh, $x = some $fresh ∧ $b)"))
      case Prod(a, b)  => any(List(occurs(y, s"$x.1", a, target, seen), occurs(y, s"$x.2", b, target, seen)))
      // A function can hold what it returns (or takes): what the view must list of it cannot be stated.
      case Fun(text)   =>
        val names = """[A-Za-z_][\w.]*""".r.findAllIn(text).toSet
        val t = target match { case Name(n) => Some(n); case _ => None }
        if t.exists(n => names(n) || names.exists(m => typeDecls.get(m).exists(_.uses.contains(n)))) then
          Left(s"the result is a function ($text), which can hold a ${t.getOrElse("")}: what the view must list of it cannot be stated")
        else Right(None)
      case Name(n) => typeDecls.get(n) match
        case None => Right(None)
        case Some(_) if seen(n) => Left(s"$n is recursive")
        case Some(d) => d.ctors match
          case List(("mk", fields)) => any(fields.map((f, ft) => occurs(y, s"$x.$f", parse(ft), target, seen + n)))
          case ctors =>
            val cases = ctors.map { (c, fs) =>
              val vars = fs.indices.map(i => s"${fresh}$i").toList
              (c, vars, any(fs.zip(vars).map { case ((_, ft), v) => occurs(y, v, parse(ft), target, seen + n) }))
            }
            cases.collectFirst { case (_, _, Left(w)) => w }.toLeft {
              Option.when(cases.exists(_._3.exists(_.isDefined)))(cases.map { (c, vs, b) =>
                s"| $n.$c${vs.map(" " + _).mkString} => ${b.toOption.flatten.getOrElse("False")}"
              }.mkString(s"(match $x with ", " ", ")"))
            }

  /** Each paired with the call's input of the rule's first type, when one input has it; Left when it cannot be stated. */
  def coverage(n: Node[?], inv: Node[?]): Either[String, Option[(String, Ctx)]] =
    val stated = for
      post <- n.post
      rule <- inv.rule.map(_.params.map(_._2))
      what <- rule.lift(1)
      view <- formalKeeps(n).collectFirst { case (i, v) if i eq inv => v }
      ts = post.params.map(_._2)
      result <- ts.lastOption
      target = parse(what)
      // Of the domain (a record, an opaque thing), not a number or string every result may hold for other reasons.
      if (target match { case Name(t) => typeDecls.contains(t) || isOpaque(t); case _ => false })
    yield
      val (v, vo) = app(qualified(n, s"view_${inv.id}"), ctx(view))
      // The inputs of the rule's first type (who a call shows things to).
      val rs = ts.init.zipWithIndex.filter((t, _) => rule.headOption.exists(r => parse(t) == parse(r))).map(_._2)
      occurs("y'", s"x${ts.size - 1}", parse(result), target).map(_.map { occ =>
        val pair = rs match { case List(i) => s"p.1 = x$i ∧ p.2 = y'"; case _ => "p.2 = y'" }
        val (vars, xs) = LeanText.call(ts)
        (s"∀ $vars, ∀ (y' : $what), $occ → ∃ p ∈ $v $xs, $pair", vo)
      }).flatMap(c => if c.isDefined && rs.size > 1 then
          Left(s"${rs.size} inputs are of the rule's first type: the view's pairs cannot be tied to one of them")
        else Right(c))
    stated.getOrElse(Right(None))

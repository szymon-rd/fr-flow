package frflow.dsl.compiled.threads

import frflow.core.threads.{Arm, Pattern, Term as Rocq, Ty}
import frflow.dsl.compiled.threads.reading.{Res, Step}

/** A `match`, and a test for null.
  *
  *   - On an `Option` or an `Either`, it is Rocq's match on `option` or on a sum (`Left` is `inl`, `Right` is
  *     `inr`), one arm for each constructor, in the order the cases first name them. A case with a guard is `if
  *     guard then … else` the next case that takes the same constructor.
  *   - On a value that may be null, `case null` is `None` and the other case `Some`: the variable it binds is
  *     the value, cast to its class where it is held as a `val`. `if v == null then a else b` is the same match:
  *     on a value, `v` names what it holds in `b`; on a `var`, a new name does.
  *   - With one case `_`, it evaluates what it is on and goes on.
  */
private[threads] trait ReadMatch extends ReadControl:
  import q.reflect.*

  /** A case: the constructor it takes (none: any), the variable it binds, its guard and its body. */
  private final case class Clause(ctor: Option[String], binds: Option[Symbol], guard: Option[Term], body: Term)

  private def isNull(t: Tree): Boolean = t match
    case Literal(NullConstant()) => true
    case _                       => false

  def matched(on: Term, cases: List[CaseDef], goal: Goal)(using Env): (List[Step], Done) = cases match
    case List(CaseDef(Wildcard(), None, body))     => block(List(on), body, goal)
    case _ if cases.exists(c => isNull(c.pattern)) =>
      val scrutinee = value(expr(on))
      val arms = cases.map(nullCase(_, scrutinee.ty, repr(on.tpe), goal))
      (scrutinee.steps, Done(Rocq.Match(scrutinee.term, arms.map(_._1)), unified(arms.map(_._2))))
    case _                                         => split(value(expr(on)), cases.map(clause), goal)

  private def nullCase(c: CaseDef, held: Ty, declared: Ty, goal: Goal)(using env: Env): (Arm, Done) =
    val content = held match
      case Ty.Of("option", of) => of
      case other               => refuse(s"a test for null of a value of type $other")
    c match
      case CaseDef(p, None, body) if isNull(p)        => armed(Pattern.of("None"), Nil, tail(body, goal))
      case CaseDef(b @ Bind(n, Wildcard()), None, body) =>
        val bound = valueAs(coerceAs(Res.value(Rocq.Ref(n), content), declared, n), n)
        armed(Pattern.of("Some", n), bound.steps, tail(body, goal)(using env.named(b.symbol, n, declared)))
      case CaseDef(Wildcard(), None, body)            => armed(Pattern.of("Some", "_"), Nil, tail(body, goal))
      case other                                      => refuse(s"the case ${other.pattern.show} of a test for null")

  private def armed(pattern: Pattern, steps: List[Step], done: Done): (Arm, Done) =
    (Arm(pattern, Step.before(steps, done.term)), done)

  /** `if v == null then whenTrue else whenFalse` (or `!=`), `v` a variable that may be null. */
  def nullTest(cond: Term, whenTrue: Term, whenFalse: Term, goal: Goal)(using env: Env): Option[Done] = cond match
    case Apply(Select(id: Ident, op @ ("==" | "!=" | "eq" | "ne")), List(n)) if isNull(n) =>
      val (whenNull, whenSet) = if op == "==" || op == "eq" then (whenTrue, whenFalse) else (whenFalse, whenTrue)
      val arms = env.vars.get(id.symbol) match
        case Some(Slot.Tested(option, content, declared))        =>
          val bound = valueAs(coerceAs(Res.value(Rocq.Ref(id.name), content), declared, id.name), id.name)
          Some((option, armed(Pattern.of("Some", id.name), bound.steps,
            tail(whenSet, goal)(using env.named(id.symbol, id.name, declared)))))
        case Some(Slot.Mutable(name, ty @ Ty.Of("option", of), _)) =>
          val known = fresh(of, Set.empty)
          val inner = (env + (id.symbol -> Slot.Mutable(name, ty, Some(known)))).local(known, of)
          Some((name, armed(Pattern.of("Some", known), Nil, tail(whenSet, goal)(using inner))))
        case _                                                   => None
      arms.map { (on, some) =>
        val none = armed(Pattern.of("None"), Nil, tail(whenNull, goal))
        val both = if whenNull eq whenTrue then List(none, some) else List(some, none)
        Done(Rocq.Match(Rocq.Ref(on), both.map(_._1)), unified(both.map(_._2))) }
    case _                                                                                => None

  private def clause(c: CaseDef): Clause = c.pattern match
    case Wildcard()                                    => Clause(None, None, c.guard, c.rhs)
    case TypedOrTest(u: Unapply, _)                    => unapplied(u, c)
    case u: Unapply                                    => unapplied(u, c)
    case id: Ident if id.symbol.fullName == "scala.None" => Clause(Some("None"), None, c.guard, c.rhs)
    case other                                         => refuse(s"the pattern ${other.show}")

  private def unapplied(u: Unapply, c: CaseDef): Clause =
    val ctor = u.fun.symbol.owner.name.stripSuffix("$") match
      case "Some"  => "Some"
      case "Left"  => "inl"
      case "Right" => "inr"
      case other   => refuse(s"a pattern of $other")
    u.patterns match
      case List(b @ Bind(_, Wildcard())) => Clause(Some(ctor), Some(b.symbol), c.guard, c.rhs)
      case List(Wildcard())              => Clause(Some(ctor), None, c.guard, c.rhs)
      case _                             => refuse(s"the pattern ${c.pattern.show}")

  /** The constructors of the type matched on, each with the type of what it holds. */
  private def constructors(ty: Ty): List[(String, Option[Ty])] = ty match
    case Ty.Of("option", of) => List("None" -> None, "Some" -> Some(of))
    case Ty.Sum(l, r)        => List("inl" -> Some(l), "inr" -> Some(r))
    case other               => refuse(s"a match on a value of type $other")

  private def split(on: Res, clauses: List[Clause], goal: Goal)(using Env): (List[Step], Done) =
    val all = constructors(on.ty)
    val order = (clauses.flatMap(_.ctor) ++ all.map(_._1)).distinct
    val arms = order.map(k => arm(k, all.toMap.apply(k), clauses.filter(_.ctor.forall(_ == k)), goal))
    (on.steps, Done(Rocq.Match(on.term, arms.map(_._1)), unified(arms.map(_._2))))

  /** The arm of one constructor: the cases that take it, in order. */
  private def arm(ctor: String, holds: Option[Ty], clauses: List[Clause], goal: Goal)(using env: Env): (Arm, Done) =
    val bound = clauses.filter(_.ctor.nonEmpty).flatMap(_.binds)
    val name = bound.map(_.name).distinct match
      case Nil       => "_"
      case List(one) => one
      case several   => refuse(s"cases that name what $ctor holds ${several.mkString(" and ")}")
    val inner = holds.fold(env)(ty => bound.foldLeft(env)((e, s) => e.named(s, name, ty)))
    armed(Pattern.of(ctor, holds.map(_ => name).toList*), Nil, decide(clauses, goal)(using inner))

  private def decide(clauses: List[Clause], goal: Goal)(using Env): Done = clauses match
    case Nil                                 => refuse("a match that does not take every case")
    case Clause(_, _, None, body) :: _       => tail(body, goal)
    case Clause(_, _, Some(g), body) :: rest =>
      val cond = value(coerce(expr(g), Ty.Bool))
      val (yes, no) = (tail(body, goal), decide(rest, goal))
      Done(Step.before(cond.steps, Rocq.If(cond.term, yes.term, no.term)), unified(List(yes, no)))

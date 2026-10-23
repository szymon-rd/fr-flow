package frflow
package lean

import LeanType.*

/** What a result holds, for the coverage of an invariant's view: a contract's view of an invariant must
  * list every value of the rule's type the result holds (`cover_<invariant>`).
  */
final class Coverage(kb: KnowledgeBase, refinement: Refinement):
  import refinement.*
  import refinement.vocabulary.*

  private val typeDecls: Map[String, TypeDecl] = kb.types.map(t => t.name -> t).toMap

  /** `y` occurs in `x` of type `t`, as a Lean proposition: None if a value of `t` can never hold one of
    * `target`; Left for a type FrFlow cannot unfold (a recursive one).
    */
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

  /** The inputs of a contract of the rule's first type (who a call shows things to). */
  private def readers(inputs: List[String], rule: List[String]): List[Int] =
    inputs.zipWithIndex.filter((t, _) => rule.headOption.exists(r => parse(t) == parse(r))).map(_._2)

  /** That a contract's view of an invariant lists every value of the rule's type the result holds,
    * each paired with the call's input of the rule's first type (when exactly one input has it): a view
    * cannot leave out, or pair with someone else, what the result shows. Left when it cannot be stated;
    * else the statement (over the result as `x<last>`) and the terms it mentions.
    */
  def coverage(n: Node[?], inv: Node[?]): Either[String, Option[(String, Ctx)]] =
    val stated = for
      post <- n.post
      rule <- inv.rule.map(_.params.map(_._2))
      what <- rule.lift(1)
      view <- formalKeeps(n).collectFirst { case (i, v) if i eq inv => v }
      ts = post.params.map(_._2)
      result <- ts.lastOption
      target = parse(what)
      // About a value of the domain (a record, an opaque thing), not a number or a string, which every
      // result may hold for other reasons.
      if (target match { case Name(t) => typeDecls.contains(t) || isOpaque(t); case _ => false })
    yield
      val (v, vo) = app(qualified(n, s"view_${inv.id}"), ctx(view))
      val rs = readers(ts.init, rule)
      occurs("y'", s"x${ts.size - 1}", parse(result), target).map(_.map { occ =>
        val pair = rs match { case List(i) => s"p.1 = x$i ∧ p.2 = y'"; case _ => "p.2 = y'" }
        val (vars, xs) = LeanText.call(ts)
        (s"∀ $vars, ∀ (y' : $what), $occ → ∃ p ∈ $v $xs, $pair", vo)
      }).flatMap(c => if c.isDefined && rs.size > 1 then
          Left(s"${rs.size} inputs are of the rule's first type: the view's pairs cannot be tied to one of them")
        else Right(c))
    stated.getOrElse(Right(None))

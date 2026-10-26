package frflow
package testing

import scala.util.Try

/** Values to show something is not vacuous: of a type, as the tests draw them (the given generators, and what always
  * holds of the type), smallest first; and cases on which a condition holds, as Scala evaluates it.
  */
private[frflow] object Witnesses:
  private val Draws = 300

  /** Up to `count` values of `t`, as the tests draw them, the empty value of a list or an option first: those the
    * `rules` hold of, as Scala runs them (all, where it cannot).
    */
  def values(kb: KnowledgeBase, t: LeanType[?], count: Int, rules: List[Def[?]] = Nil): List[Any] =
    val plan = planOf(kb)
    def meets(v: Any) = rules.forall(d =>
      Try(Watch.within(Watch.overNumbers(List(v)))(Fn.call(d.fn, List(v)).asInstanceOf[Boolean])).getOrElse(true))
    val drawn =
      (0 until Draws).iterator.flatMap(i => Try(Draw(Testing.random(3, i), 1 + i % 4, plan).value(t)).toOption)
    (empty(t).iterator ++ drawn).filter(v => Try(kb.holds(t)(v)).getOrElse(false) && meets(v)).distinct.take(count)
      .toList

  /** A case of the binders on which `condition` holds, as Scala evaluates it: none when none drawn does, or Scala
    * cannot evaluate it.
    */
  def caseOf(kb: KnowledgeBase, bs: List[Binder], condition: Tree): Option[List[Any]] =
    val plan = planOf(kb)
    val run = Try(Eval.compile(condition)).toOption
    run.flatMap { f =>
      def holds(vals: List[Any]) =
        Try(Bindings.within(kb.opCode ++ kb.definitionBindings)(f(bs.zip(vals).toMap).asInstanceOf[Boolean]))
          .getOrElse(false)
      (0 until Draws).iterator
        .flatMap(i => Try(bs.map(b => Draw(Testing.random(5, i), 1 + i % 4, plan).value(b.tpe))).toOption).find(holds)
    }

  private def planOf(kb: KnowledgeBase): Plan =
    val keyOf = Plan(Map.empty, Map.empty, Nil, Testing.opaques(kb))
    Plan(kb.generators.toMap.map((t, g) => keyOf.key(t) -> g), Map.empty, Nil, Testing.opaques(kb), holds = kb.holds)

  private def empty(t: LeanType[?]): Option[Any] = t.shape match
    case frflow.types.Shape.ListOf(_)   => Some(Nil)
    case frflow.types.Shape.OptionOf(_) => Some(None)
    case _                              => None

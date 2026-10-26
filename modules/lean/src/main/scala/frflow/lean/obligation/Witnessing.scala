package frflow
package lean
package obligation

import frflow.example.Example
import frflow.lean.printing.{Layout, LeanText, VocabularyModules}
import frflow.protocol.snapshot.Consistency.Kind
import frflow.testing.Witnesses

/** What Lean is asked of the knowledge base as a whole (docs/DAG.md §3a): that the statements at the bottom of the
  * DAG hold together, each group sharing open terms with a witness for them (an equation a statement gives,
  * `granted(held, request) === …`, or proven code), so the proven steps above carry it up; and that nothing they rest
  * on is vacuous: each `always` admits a value, each store's start some state, each claim's condition some case.
  */
final class Witnessing(kb: KnowledgeBase, refinement: Refinement, layout: Layout, vocabularyModules: VocabularyModules):
  import refinement.*
  import refinement.vocabulary.*
  private val K = kb.name

  /** One thing asked: the theorems that may show it (any one does), what they are given, and what is missing. */
  final case class Asked(kind: Kind, about: List[Node[?]], theorems: List[(String, String)], witness: String,
      missing: Option[String])

  lazy val asked: List[Asked] = together ++ admits ++ starts ++ conditions

  /** The module: every theorem asked, each proven by the witness it is given. */
  lazy val file: String =
    val nodes = asked.flatMap(_.about).filter(formal).distinctBy(_.id)
    val rules = kb.nodes.flatMap(n => n.holds ++ n.initially)
    val uses = (layout.types :: vocabularyModules.modulesFor(rules, Nil) ++ nodes.map(n => layout.spec(n.id))).distinct
    val body =
      asked.flatMap(a => a.theorems.map((name, text) => s"${LeanText.doc(describe(a))}theorem $name : $text\n\n"))
    LeanText.module(uses, s"$K.Consistency", body.mkString, Some(K))

  def describe(a: Asked): String = a.kind match
    case Kind.Together  => s"Some meaning of their terms meets ${a.about.map(_.id).mkString(", ")}: ${a.witness}."
    case Kind.Admits    => s"Some value holds what ${a.about.map(_.id).mkString} says always holds: ${a.witness}."
    case Kind.Starts    => s"Some state meets what ${a.about.map(_.id).mkString} says the store starts with: " +
      s"${a.witness}."
    case Kind.Condition => s"Some case meets the condition of ${a.about.map(_.id).mkString}: ${a.witness}."

  // The statements at the bottom: formal, with no parts, and not an `always` (a hypothesis of the others, shown not
  // vacuous below), grouped by the open terms they share.
  private def bottom: List[Node[?]] = kb.nodes.filter(n => formal(n) && !n.isAlways && leafy(n))

  private def groups: List[List[Node[?]]] =
    bottom.foldLeft(List.empty[List[Node[?]]]) { (gs, n) =>
      val terms = claimCtx(n).names.toSet
      val (joined, apart) = gs.partition(g => g.exists(m => claimCtx(m).names.exists(terms)))
      apart :+ (joined.flatten :+ n)
    }

  private def together: List[Asked] = groups.map { g =>
    val opens = Ctx.all(g.map(claimCtx))
    val claims = g.map(claim(_)._1).mkString(" ∧ ")
    val name = s"together_${g.head.id}"
    if opens.opaques.nonEmpty then
      Asked(Kind.Together, g, Nil, "", Some(s"they leave the types ${opens.opaques.mkString(", ")} open: define them"))
    else
      val found = opens.params.map(p => p -> witness(p, g))
      val missing = found.collect { case (p, None) => why(p) }
      val ws = found.collect { case (p, Some(w)) => p -> w }
      val statement = if opens.params.isEmpty then claims else s"∃ ${binders(opens)}, $claims"
      val proof =
        if ws.isEmpty then "by\n  frflow_auto"
        else s"by\n  refine ⟨${ws.map(_._2._1).mkString(", ")}, ?_⟩\n  frflow_auto"
      val chosen = if ws.isEmpty then "they leave nothing open" else ws.map((p, w) => s"$p as ${w._2}").mkString(", ")
      Asked(Kind.Together, g, Option.when(missing.isEmpty)(name -> s"$statement := $proof").toList, chosen,
        Option.when(missing.nonEmpty)(missing.mkString("; ")))
  }

  /** What an open term is in a witness: what an equation of a statement in the group gives it, or its proven code. */
  private def witness(p: String, group: List[Node[?]]): Option[(String, String)] =
    val equation = for
      n <- group.find(n => n.op.exists(_.name == p))
      post <- n.post if !n.isFlow
      (bs, e) <- Equations.answerOf(post)
      lifted = Lifted(() => (bs, Term(e, Equations.resultType(n))), null, "")
      if ctx(lifted).isEmpty
    yield (resolve(lifted.lean), s"${n.id} says")
    val code = kb.onOp.getOrElse(p, Nil).flatMap(provenImpl).headOption.filter(d => defCtx(d).isEmpty)
      .map(d => (s"$K.${d.name}", s"its proven code, ${d.name}"))
    equation.orElse(code).orElse(value(p))

  /** A value of a term no statement is about (the data a system is given, `grants`): one the tests draw. */
  private def value(p: String): Option[(String, String)] =
    for
      param <- kb.params.find(_.name == p) if !kb.isOp(p)
      v <- scala.util.Try(Witnesses.values(kb, param.termType, 1)).toOption.flatMap(_.headOption)
      lean <- scala.util.Try(LeanPrinter().value(v, param.termType)).toOption
    yield (lean, s"the value ${Example.show(v)}")

  private def why(p: String): String =
    val tested = kb.onOp.getOrElse(p, Nil).exists(c => kb.implementation(c).exists(_.proven.isEmpty))
    if tested then s"$p: its code is tested Scala, evidence and not proof; say what it equals (a statement $p(…) === …)"
    else s"$p: nothing says what it equals, and no proven code gives it; say what it equals (a statement $p(…) === …)"

  private def admits: List[Asked] = kb.nodes.flatMap(n => n.holds.map(r => n -> r)).map { (n, rule) =>
    valued(Kind.Admits, n, rule, s"admits_${n.id}")
  }

  private def starts: List[Asked] = kb.nodes.flatMap(n => n.initially.map(r => n -> r)).map { (n, rule) =>
    valued(Kind.Starts, n, rule, s"starts_${n.id}")
  }

  /** Some value of the rule's type holds it: each of a few drawn values, smallest first, tried as the witness. */
  private def valued(kind: Kind, n: Node[?], rule: Def[?], name: String): Asked =
    val t = rule.lifted.built._1.head.tpe
    val tpe = Types.walk(t).lean
    val values = scala.util.Try(Witnesses.values(kb, t, 3, Some(rule))).getOrElse(Nil)
    val (f, _) = code(rule)
    val theorems = values.zipWithIndex.flatMap { (v, i) =>
      scala.util.Try(LeanPrinter().value(v, t)).toOption
        .map(lv => s"${name}_$i" -> s"∃ (x : $tpe), $f x := ⟨$lv, by frflow_auto⟩")
    }
    Asked(kind, List(n), theorems, values.map(Example.show).mkString(" or "),
      Option.when(theorems.isEmpty)(s"no value of ${Types.scala(t)} was drawn to try"))

  /** Each claim stated as a condition and what follows from it: some generated case meets the condition. */
  private def conditions: List[Asked] = kb.nodes.filter(n => formal(n) && !n.isAlways).flatMap { n =>
    for
      f <- n.formula.toList
      (bs, condition) <- Equations.conditionOf(f).toList
    yield
      val lifted = Lifted(() => (bs, Term(condition, summon[frflow.types.LeanType[Boolean]])), null, "")
      val name = s"condition_${n.id}"
      if !ctx(lifted).isEmpty then Asked(Kind.Condition, List(n), Nil, "",
        Some(s"its condition reads ${ctx(lifted).names.mkString(", ")}, open terms: no case is drawn of them"))
      else Witnesses.caseOf(kb, bs, condition) match
        case None => Asked(Kind.Condition, List(n), Nil, "", Some("no generated case meets its condition"))
        case Some(vals) =>
          val args = bs.zip(vals).map((b, v) => scala.util.Try(LeanPrinter().value(v, b.tpe)).toOption)
          val shown = bs.zip(vals).map((b, v) => s"${b.hint} = ${Example.show(v)}").mkString(", ")
          val theorem = s"(${resolve(lifted.lean)}) ${args.flatten.mkString(" ")} := by\n  frflow_eval"
          if args.exists(_.isEmpty) then
            Asked(Kind.Condition, List(n), Nil, shown, Some("Lean has no value for the case"))
          else Asked(Kind.Condition, List(n), List(name -> theorem), shown, None)
  }

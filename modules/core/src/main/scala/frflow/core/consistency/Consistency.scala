package frflow.core.consistency

import cats.syntax.all.*
import frflow.core.analysis.outside.Guards
import frflow.core.analysis.resolution.{Callees, Constrained}
import frflow.core.code.Code
import frflow.core.expr.{Expr, Exprs}
import frflow.core.name.{DefName, NodeId, SourceText, SymbolName}
import frflow.core.spec.{NodeKind, Range, Written}
import frflow.core.term.interpret.{Guarded, ToExpr}
import frflow.core.Theory
import frflow.core.ty.Ty
import frflow.core.vocab.SymbolType

/** The consistency and vacuity obligations of a theory (owner §15, §18), derived from it alone: no example is read.
  * The bottom statements and the premises beside them, split into groups that share open values, each with the
  * witnesses derived for it; each `always[T]` and each claim's condition, to be shown possible.
  */
object Consistency:
  def of(t: Theory): List[Group] =
    val r = read(t)
    sharing(t, r) ++ premised(t, r)

  /** `inhabited_` of every `always[T]`, claimed or assumed, with every other rule on its type (`meets`);
    * `satisfiable_` of every claim's condition. Reported, not gated (2.9).
    */
  def vacuity(t: Theory): List[Vacuity] = t.nodes.map(_.node).flatMap(n => n.statement.range.toList.flatMap {
    case Range.Made(ty)                                       => List(Vacuity.Inhabited(n.id, ty))
    case Range.Possible if n.statement.kind == NodeKind.Claim =>
      n.statement.said.toList.flatMap(f => Conditions.of(f.term, ToExpr).zipWithIndex.map((c, i) =>
        Vacuity.Satisfiable(n.id, i, c.over.map(_.ty))))
    case _                                                   => Nil
  })

  /** What the value an `inhabited_` asks for meets: every `always[T]` on its type together, so two that contradict
    * show.
    */
  def meets(t: Theory, ty: Ty): List[DefName] = t.nodes.map(_.node).collect {
    case x if x.statement.range.contains(Range.Made(ty)) => DefName(x.id.value)
  }

  /** The statements no proven step gives: the prover states them, about every possible value, with no parts. The claims
    * among them and the assumptions beside them (an outside system's promise) are the bottom of the theory.
    */
  def bottom(t: Theory): List[NodeId] = t.nodes.map(_.node).collect {
    case n if n.statement.stated && n.statement.range.contains(Range.Possible) &&
        t.refinement.parts(n.id).isEmpty => n.id
  }

  /** What a statement leaves open: the Declarations it mentions, and the Definitions no proof or fixed value gives
    * a meaning (plain Scala, tested; or none), its own and those the proven code standing in it leaves open, through
    * the proven code that code calls.
    */
  def open(t: Theory, id: NodeId): List[SymbolName] =
    Callees.reaching(t, Constrained.of(t, id)).filter(isOpen(t, _))

  /** What a proven Definition's code leaves open, through the proven code it calls; nothing of any other. */
  def reach(t: Theory, s: SymbolName): List[SymbolName] =
    Callees.reaching(t, List(s)).filter(x => x != s && isOpen(t, x))

  private def isOpen(t: Theory, s: SymbolName): Boolean = t.vocabulary.symbol(s).nonEmpty &&
    (Constrained.isDeclaration(t, s) || t.code.attached.get(s).forall(a => a.code.proven.isEmpty && !fixed(a.code)))

  /** What a statement takes for every value code is given: the Definitions provided where the code runs, its own and
    * those the proven code standing in it reaches, through the code that code calls.
    */
  def provided(t: Theory, id: NodeId): List[SymbolName] =
    Callees.reaching(t, Constrained.of(t, id)).filter(isProvided(t, _))

  private def isProvided(t: Theory, s: SymbolName): Boolean = t.code.attached.get(s).exists(_.code == Code.Provided)

  /** A value fixed in the model or provided. */
  private def fixed(c: Code): Boolean = c match
    case Code.Valued(_) | Code.Provided => true
    case _                              => false

  /** Joined by open values and by the provided values an assumption pins: every statement mentioning a pinned value
    * is in its group, which solves it once (two groups choosing it apart would not show they hold together), and an
    * assumption whose only value is a pinned one has a group too. Each other value provided is universal, with the
    * assumptions at the bottom about such values alone as premises: what the world outside is trusted to give.
    */
  private def sharing(t: Theory, r: Read): List[Group] =
    joined(r.ids.map(id => id -> (r.open(id) ++ r.provided(id).filter(r.pinned)).distinct).filter(_._2.nonEmpty))
      .map { (ids, keys) =>
        val fromOutside = (ids.flatMap(Constrained.of(t, _)).filter(isProvided(t, _)) ++ ids.flatMap(r.provided))
          .distinct
        val opens = keys.filterNot(r.pinned) ++ fromOutside.filter(r.pinned)
        val universal = fromOutside.filterNot(r.pinned)
        Group.Sharing(ids, opens, universal, witnesses(t, ids, opens),
          r.premises.filter(p => r.provided(p).forall(universal.contains)))
      }

  /** The bottom statements as consistency reads them, each once: what each leaves open and takes provided, the
    * provided values an assumption pins, and the premises: the assumptions at the bottom about unpinned provided
    * values alone, what the world outside is trusted to give.
    */
  private final case class Read(ids: List[NodeId], open: Map[NodeId, List[SymbolName]],
      provided: Map[NodeId, List[SymbolName]], pinned: Set[SymbolName], premises: List[NodeId])

  private def read(t: Theory): Read =
    val ids = bottom(t)
    val words = ids.map(id => id -> Callees.reaching(t, Constrained.of(t, id))).toMap
    val opens = words.view.mapValues(_.filter(isOpen(t, _))).toMap
    val outside = words.view.mapValues(_.filter(isProvided(t, _))).toMap
    val pinned = ids.flatMap(id => outside(id).filter(pins(t, id, _))).toSet
    Read(ids, opens, outside, pinned, ids.filter(id => t.node(id).exists(_.statement.kind == NodeKind.Assumption) &&
      opens(id).isEmpty && outside(id).nonEmpty && !outside(id).exists(pinned)))

  /** The premises joined while they share a provided value, each set with the witnesses derived for its values (a
    * list none bounds, empty), in the order they are bound.
    */
  private def premised(t: Theory, r: Read): List[Group] =
    joined(r.premises.map(id => id -> r.provided(id))).map { (ids, values) =>
      val ws = witnesses(t, ids, values).map {
        case Witness.Missing(s) if listed(t, s) => Witness.Empty(s)
        case w                                  => w
      }
      Group.Premises(ids, values, ws.sortBy(w => values.indexOf(w.meaningOf)))
    }

  private def listed(t: Theory, s: SymbolName): Boolean = t.vocabulary.symbol(s).map(_.ty).exists {
    case SymbolType.Typed(Ty.ListOf(_)) => true
    case _                              => false
  }

  /** Whether an assumption of the group equates the provided value to a term (`state === stateAfter(history)`): the
    * value is then solved by that equation, like an open one, for every value meeting the group's assumptions is
    * that term's (step 12 ruling); a provided value nothing pins stays universal.
    */
  private def pins(t: Theory, id: NodeId, p: SymbolName): Boolean =
    t.node(id).filter(_.statement.kind == NodeKind.Assumption).flatMap(_.statement.said).exists(f =>
      Equations(Nil, _ => Nil, _ => Nil).defining(id, f.value, p).exists {
        case Witness.Equation(_, _, _) => true
        case _                         => false
      })

  /** Statements joined while they share an open value, in the model's order. */
  private def joined(xs: List[(NodeId, List[SymbolName])]): List[(List[NodeId], List[SymbolName])] =
    xs.foldLeft(List.empty[(List[NodeId], List[SymbolName])]) { case (groups, (id, opens)) =>
      val (touching, apart) = groups.partition(_._2.exists(opens.contains))
      apart :+ (touching.flatMap(_._1) :+ id, (touching.flatMap(_._2) ++ opens).distinct)
    }

  /** The group solved in substitution order (R14.6): an equation or bound whose other side mentions no value still
    * open witnesses its value, which then stands for itself in the rest; repeated until none is left to solve. What
    * no equation reaches (a cycle, or nothing said) is tested Scala's evidence, or missing. In solving order.
    */
  private def witnesses(t: Theory, ids: List[NodeId], opens: List[SymbolName]): List[Witness] =
    def solve(left: List[SymbolName], solved: List[Witness]): List[Witness] =
      val equations = Equations(left, reach(t, _), Callees.calledBy(t, _))
      left.iterator.flatMap(s => ids.iterator.flatMap(id => t.node(id).flatMap(_.statement.said)
        .flatMap(f => equations.defining(id, f.value, s)))).nextOption() match
        case Some(w) => solve(left.filterNot(_ == w.meaningOf), solved :+ w)
        case None    => solved ++ left.map(s => if tested(t, s) then Witness.Tested(s) else Witness.Missing(s))
    solve(opens, Nil)

  private def tested(t: Theory, s: SymbolName): Boolean =
    t.code.attached.get(s).exists(_.code.scala.nonEmpty)

  /** `∃ xs, A`: the `i`-th condition of `n`'s claim with the variables above it, written as the claim is, each
    * variable with what always holds of it, as the claim's own (`Guards`): a value code can make.
    */
  def condition(t: Theory, n: NodeId, i: Int): Option[Written[Expr]] =
    t.node(n).flatMap(_.statement.said).map(f => Written.formula(Guarded.of(Conditions.satisfiable(f.term, i),
      Guards.of(t)), SourceText(s"${f.source.value} (condition ${i + 1})")))

  /** What a condition leaves open, in order: the Definitions and Declarations it mentions, through the defines it
    * calls too, but proven code.
    */
  def opens(t: Theory, c: Written[Expr]): List[SymbolName] =
    val own = Exprs.mentions(c.value)
    (own |+| t.vocabulary.closure(own.defines).foldMap(d => Exprs.mentions(d.lambda.body))).symbols
      .filter(s => t.vocabulary.symbol(s).nonEmpty && t.code.attached.get(s).forall(_.code.proven.isEmpty))

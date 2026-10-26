package frflow.core.checking

import frflow.core.analysis.{Callees, Constrained, Outsides, Premise, Premises, Scope}
import frflow.core.code.Code
import frflow.core.consistency.{Consistency, Group, Standing, Vacuity}
import frflow.core.expr.OutsideFact
import frflow.core.name.{ModelName, NodeId, OpName, SymbolName}
import frflow.core.spec.{CallForms, Range, Statement}
import frflow.core.ty.Ty
import frflow.core.Theory

/** How a statement is checked, derived from its formula, its place and what defines each Definition it mentions
  * (owner §15): what `show` lists beside it, so a reader sees every way it is held to account. Several apply to
  * one statement.
  */
enum Checking:
  /** Proven from its parts (`complete`). */
  case FromParts(parts: List[NodeId])
  /** Checked against what gives a Definition it mentions its meaning: proven code (`impl`), a fixed value
    * (substituted), a value provided where the code runs (stated for every one).
    */
  case AgainstCode(definition: SymbolName, code: Code)
  /** Tested against the Definition's plain Scala on generated cases: call by call where the statement reads as its
    * call, else the statement evaluated whole on its drawn variables, every Definition given its meaning.
    */
  case TestedAgainst(definition: SymbolName, whole: Boolean)
  /** The Definition's plain Scala cannot be tested against it: the statement has no Scala value (it quantifies over
    * every value of a type). Unless its parts prove it, nothing checks it (`status` warns).
    */
  case NotTested(definition: SymbolName)
  /** Taken as a hypothesis by the proofs of code calling the Definitions it mentions. */
  case AssumedByCallers(definitions: List[SymbolName])
  /** `always[T]`: met where a value of `ty` is made (each of `makers`' results: proven, or tested at its boundary),
    * or each store operation's result on its model, `made_<op>`), entering values by the outside facts it rests on; a
    * hypothesis on every value of `ty` in Lean.
    */
  case WhereMade(ty: Ty, makers: List[SymbolName], models: List[(ModelName, OpName)])
  /** Kept by every run of these programs (`cover_`), from the state the store starts in. */
  case KeptBy(programs: List[SymbolName])
  /** A fact about the outside its check rests on, and the assumption saying it. */
  case RestsOn(premise: Premise, assumption: Option[NodeId])
  /** At the bottom: shown consistent with the statements sharing its open values (`consistent`). */
  case Consistent(group: List[NodeId], standing: Standing)
  /** Shown not vacuous: its `always` admits a value, its conditions can hold. */
  case Possible(shown: List[Vacuity])
  /** Trusted: an outside system's promise, its code tested against it where there is code. */
  case Trusted
  /** A fact about the world outside the code: a rule of FrFlow's rests on it. */
  case Outside(fact: OutsideFact)
  /** A store behaving as its model: the store's code is tested against the model (`checkedAgainst`). */
  case StoreCodeTested(implementations: Int)
  /** Nothing checks it yet: no parts, no code. */
  case Unchecked

object Checking:
  def of(t: Theory, id: NodeId): List[Checking] = t.node(id).map(_.statement).toList.flatMap {
    case s @ Statement.Assumption(_) => s.outside.fold(Trusted :: callers(t, id))(outside(t, _))
    case s @ Statement.Claim(_, _)   => claimed(t, id, s) ++ rests(t, id) ++ bottom(t, id) ++ possible(t, id)
    case Statement.Design(_)         => Nil
  }

  private def claimed(t: Theory, id: NodeId, s: Statement): List[Checking] = s.range.toList.flatMap {
    case r @ Range.Made(ty) =>
      List(WhereMade(ty, Scope.of(t, id), Scope.modelMakers(t, r).map((m, sig) => m.name -> sig.name)))
    case Range.Reached(_)  => List(KeptBy(Scope.of(t, id)))
    case Range.Possible    =>
      val code = Constrained.of(t, id).flatMap(d => t.code.attached.get(d).map(a => against(t, s, d, a.code)))
      val parts = t.refinement.parts(id)
      val fromParts = Option.when(parts.nonEmpty && Callees.of(t, id).isEmpty)(FromParts(parts)).toList
      fromParts ++ code ++ callers(t, id) match
        case Nil  => List(Unchecked)
        case some => some
  }

  /** The facts about the outside its `.assuming` lists, each with what it is a premise of. */
  /** Plain Scala is tested where the statement (per call, or whole) has a Scala value; other code is proven of. */
  private def against(t: Theory, s: Statement, d: SymbolName, code: Code): Checking = code match
    case Code.Tested(_, _) =>
      val perCall = s.call.filter(_.definition == d).map(_.posted.value.body)
      val body = perCall.orElse(s.said.map(f => CallForms.whole(f).value.body))
      if body.exists(Evaluable.of(t, _)) then TestedAgainst(d, perCall.isEmpty) else NotTested(d)
    case other             => AgainstCode(d, other)

  /** Nothing checks the statement: its parts do not prove it, no proven code or value is checked against it, and the
    * plain Scala it is about has no test it can be judged by.
    */
  def unchecked(t: Theory, id: NodeId): Boolean =
    val cs = of(t, id)
    cs.exists { case Unchecked | NotTested(_) => true; case _ => false } && !cs.exists {
      case FromParts(_) | AgainstCode(_, _) | TestedAgainst(_, _) | KeptBy(_) | WhereMade(_, _, _) => true
      case _                                                                                        => false
    }

  private def rests(t: Theory, id: NodeId): List[Checking] =
    Premises.of(t, id).map(p => RestsOn(p, Outsides.assumed(t, id, p)))

  private def bottom(t: Theory, id: NodeId): List[Checking] = Consistency.of(t).collect {
    case g @ Group.Sharing(ids, _, _, _) if ids.contains(id) => Consistent(ids, g.standing)
    case g @ Group.Start(`id`, _)                            => Consistent(List(id), g.standing)
  }

  private def possible(t: Theory, id: NodeId): List[Checking] =
    val shown = Consistency.vacuity(t).filter {
      case Vacuity.Inhabited(n, _)      => n == id
      case Vacuity.Satisfiable(n, _, _) => n == id
    }
    Option.when(shown.nonEmpty)(Possible(shown)).toList

  private def outside(t: Theory, fact: OutsideFact): List[Checking] = fact match
    case OutsideFact.BehavesAs(b, _) => List(Outside(fact), StoreCodeTested(t.code.realized.get(b).fold(0)(_.size)))
    case _                           => List(Outside(fact))

  private def callers(t: Theory, id: NodeId): List[Checking] =
    Option.when(Constrained.of(t, id).nonEmpty)(AssumedByCallers(Constrained.of(t, id))).toList

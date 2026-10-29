package frflow.core.checking

import frflow.core.analysis.{Callees, Constrained, SaysWhat, Scope}
import frflow.core.code.Code
import frflow.core.consistency.{Consistency, Group, Standing, Vacuity}
import frflow.core.expr.OutsideFact
import frflow.core.name.{ModelName, NodeId, SymbolName}
import frflow.core.spec.{CallForms, Range, Statement}
import frflow.core.ty.Ty
import frflow.core.Theory
import frflow.core.analysis.outside.{Outsides, Premise, Premises, Reads}

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
  /** Says what these Declarations are (2.7): the proven code of `code` stands in it for its Definitions; nothing is
    * proven of that code from it.
    */
  case SaysWhatIs(declarations: List[SymbolName], code: List[(SymbolName, Code)])
  /** The rules it uses (2.4): each below it, or an assumption of `always` it lists, with whether it takes it (a
    * hypothesis on a value or a world it is about). None is a part of its step.
    */
  case Rules(rules: List[(NodeId, Boolean)])
  /** Taken as a hypothesis by the proofs of code calling the Definitions it mentions. */
  case AssumedByCallers(definitions: List[SymbolName])
  /** `always[T]`: met where a value of `ty` is made (each of `makers`' results: proven, or tested at its inputs and result,
    * or each operation's result on its model, `made_<op>`), entering values by the outside facts it rests on; a
    * hypothesis on every value of `ty` in Lean.
    */
  case WhereMade(ty: Ty, makers: List[SymbolName], models: List[(ModelName, SymbolName)])
  /** Kept by every run of these programs (`cover_`), from the state the store starts in. */
  case KeptBy(programs: List[SymbolName])
  /** The plain Scala of the operations its check runs on `model` doing what the model says: tested against the model
    * on generated runs, not assumed (owner §36).
    */
  case TestedOnModel(model: ModelName, operations: List[SymbolName])
  /** A fact about the outside its check rests on, and the assumption saying it. */
  case RestsOn(premise: Premise, assumption: Option[NodeId])
  /** At the bottom: shown consistent with the statements sharing its open values (`consistent`). */
  case Consistent(group: List[NodeId], standing: Standing)
  /** Of what always holds of a store, met where the store starts, from what the assumption saying so says (`start_`).
    */
  case Starts(from: Option[NodeId], standing: Standing)
  /** Shown not vacuous: its `always` admits a value, its conditions can hold. */
  case Possible(shown: List[Vacuity])
  /** Trusted: an outside system's promise, its code tested against it where there is code. */
  case Trusted
  /** A fact about the world outside the code: a rule of FrFlow's rests on it. */
  case Outside(fact: OutsideFact)
  /** The programs changing a model's state, derived from the code (owner §31): every program calling an operation
    * whose meaning changes it.
    */
  case ChangedBy(programs: List[SymbolName])
  /** Nothing checks it yet: no parts, no code. */
  case Unchecked

object Checking:
  def of(t: Theory, id: NodeId): List[Checking] = t.node(id).map(_.statement).toList.flatMap {
    case s @ Statement.Assumption(_) =>
      s.outside.fold(Trusted :: ruled(t, id, s) ++ callers(t, id) ++ bottom(t, id) ++ possible(t, id))(outside(t, _))
    case s @ Statement.Claim(_, _)   =>
      claimed(t, id, s) ++ rules(t, id) ++ rests(t, id) ++ bottom(t, id) ++ possible(t, id)
    case Statement.Design(_)         => Nil
  }

  private def claimed(t: Theory, id: NodeId, s: Statement): List[Checking] = s.range.toList.flatMap {
    case Range.Possible if SaysWhat.is(t, id) =>
      List(SaysWhatIs(SaysWhat.declarations(t, id), Constrained.of(t, id).flatMap(d =>
        t.code.attached.get(d).map(_.code).filter(_.proven.nonEmpty).map(d -> _))))
    case Range.Possible =>
      val code = Constrained.of(t, id).flatMap(d => t.code.attached.get(d).map(a => against(t, s, d, a.code)))
      val parts = t.refinement.parts(id)
      val fromParts = Option.when(parts.nonEmpty && SaysWhat.checkedAgainst(t, id).isEmpty)(FromParts(parts)).toList
      fromParts ++ code ++ callers(t, id) match
        case Nil  => List(Unchecked)
        case some => some
    case _              => ruled(t, id, s)
  }

  /** How a rule is met: where its values are made, or by every run changing its store. */
  private def ruled(t: Theory, id: NodeId, s: Statement): List[Checking] = s.range.toList.flatMap {
    case r @ Range.Made(ty) =>
      List(WhereMade(ty, Scope.of(t, id), Scope.modelMakers(t, r).map((m, sig) => m.name -> sig.name)))
    case Range.Reached(_)   => List(KeptBy(Scope.of(t, id)))
    case Range.Possible     => Nil
  }

  /** The rules below it and the assumptions of `always` it lists, each with whether it takes it. */
  private def rules(t: Theory, id: NodeId): List[Checking] =
    val listed = t.refinement.assumed(id).filter(p => t.node(p).exists(_.statement.rule))
    val rs = (t.refinement.rules(id) ++ listed).distinct
    Option.when(rs.nonEmpty)(Rules(rs.map(r => r -> Reads.takes(t, id, r)))).toList

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
      case FromParts(_) | AgainstCode(_, _) | TestedAgainst(_, _) | KeptBy(_) | WhereMade(_, _, _) |
          SaysWhatIs(_, _) => true
      case _               => false
    }

  private def rests(t: Theory, id: NodeId): List[Checking] =
    tested(t, id) ++ Premises.of(t, id).map(p => RestsOn(p, Outsides.assumed(t, id, p)))

  /** The operations on a state whose plain Scala the check runs, by model, each model's in its order: those the code
    * it is checked against calls, those of the programs keeping its rule, and the operations making its values.
    */
  private def tested(t: Theory, id: NodeId): List[Checking] =
    val ops = t.node(id).flatMap(_.statement.range).toList.flatMap {
      case Range.Possible     => SaysWhat.checkedAgainst(t, id).toList.flatMap(_.calls.operations)
      case r @ Range.Made(_)  => keeping(t, id) ++ Scope.modelMakers(t, r).map(_._2.name)
      case Range.Reached(_)   => keeping(t, id)
    }
    t.vocabulary.models.filter(m => t.code.implemented.contains(m.name)).flatMap(m =>
      Option(m.ops.map(_.op).filter(ops.contains)).filter(_.nonEmpty).map(TestedOnModel(m.name, _)))

  private def keeping(t: Theory, id: NodeId): List[SymbolName] =
    Scope.of(t, id).flatMap(p => Callees.ofDefinition(t, p).toList.flatMap(_.calls.operations))

  private def bottom(t: Theory, id: NodeId): List[Checking] = Consistency.of(t).collect {
    case g @ Group.Sharing(ids, _, _, _) if ids.contains(id) => Consistent(ids, g.standing)
    case g @ Group.Start(`id`, from)                         => Starts(from, g.standing)
  }

  private def possible(t: Theory, id: NodeId): List[Checking] =
    val shown = Consistency.vacuity(t).filter {
      case Vacuity.Inhabited(n, _)      => n == id
      case Vacuity.Satisfiable(n, _, _) => n == id
    }
    Option.when(shown.nonEmpty)(Possible(shown)).toList

  private def outside(t: Theory, fact: OutsideFact): List[Checking] = fact match
    case OutsideFact.OnlyCodeChanges(m) =>
      List(Outside(fact), ChangedBy(t.vocabulary.model(m).toList.flatMap(Premises.writers(t, _))))
    case _                              => List(Outside(fact))

  /** The Definitions it mentions, which code may call (a Declaration is never called). */
  private def callers(t: Theory, id: NodeId): List[Checking] =
    val called = Constrained.of(t, id).filterNot(Constrained.isDeclaration(t, _))
    Option.when(called.nonEmpty)(AssumedByCallers(called)).toList

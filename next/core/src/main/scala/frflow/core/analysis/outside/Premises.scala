package frflow.core.analysis.outside

import frflow.core.code.Code
import frflow.core.expr.{Expr, Exprs, Prog, Progs}
import frflow.core.name.{DefName, ModelName, NodeId, SymbolName}
import frflow.core.spec.{Node, NodeKind, Range}
import frflow.core.ty.Ty
import frflow.core.vocab.{StateModel, SymbolType}
import frflow.core.Theory
import frflow.core.analysis.{Callees, SaysWhat, Scope}

/** What about the world outside a statement's check rests on (owner §16, §17, §21), derived from the statement and
  * the code, each to be listed by the statement's `.assuming` (owner §15: the one mechanism; `Validate` checks the
  * list, `PremiseMissing`, `PremiseNotNeeded`):
  * - a claim about a program's runs: runs on the state of each model whose operations it calls are atomic (that the
  *   operations' plain Scala does what the model says is tested, not assumed);
  * - an `always(stored)`: that, nothing outside the code changing the state, and what the state it starts in meets
  *   (the rule: every start state meets it, each run of a program changing it keeps it, so every state reached does;
  *   which programs change it is derived, `writers`);
  * - an `always[T]`: the facts of every model whose state holds a `T` (an operation making one is held to it on its
  *   model, `made_<op>`, which rests on nothing outside);
  * - and, of every claim, what values from outside meet: each assumption of `always[U]` whose guard the claim's Lean
  *   form or its `made_`/`cover_` obligations carry (on a variable it quantifies over, a world, or an input of a
  *   maker or program it is asked of; `Guards.applies` decides, as it does for the guards Lean states). An
  *   `always[T]` claim also rests on what `T`s from outside meet when an entry Definition's input or a value
  *   provided where the code runs can hold one, whether or not an assumption says it: no covered code makes those.
  */
object Premises:
  def of(t: Theory, id: NodeId): List[Premise] =
    t.node(id).filter(n => n.statement.kind == NodeKind.Claim && !SaysWhat.is(t, n.id)).toList.flatMap(n =>
      n.statement.range.toList.flatMap {
        case Range.Possible     => runs(t, id).map(m => Premise.Atomic(m.name))
        case Range.Reached(ms)  => ms.flatMap(t.vocabulary.model).flatMap(reached)
        case r @ Range.Made(ty) => passed(t, ty) ++ Scope.models(t, r).flatMap(reached)
      } ++ guarded(t, n)).distinct

  /** The programs changing `m`'s state (owner §31): those whose proven code calls an operation whose meaning writes
    * it.
    */
  def writers(t: Theory, m: StateModel): List[SymbolName] =
    val writing = m.ops.filter(op => Progs.all(op.steps).exists {
      case Prog.Write(_, _) | Prog.Modify(_, _, _) => true
      case _                                       => false
    }).map(_.op).toSet
    t.code.attached.toList.collect {
      case (s, a) if (a.code match { case Code.ProvenFlow(f) => steps(t, f); case _ => Nil }).exists(writing) => s
    }

  /** The models whose operations covered code calls: those each proven program calls, through the defines it calls.
    */
  def called(t: Theory): List[ModelName] = t.code.attached.values.toList.flatMap(a => a.code match
    case Code.ProvenFlow(f) => steps(t, f).flatMap(t.vocabulary.modelOf).map(_.name)
    case _                  => Nil).distinct

  /** The Definitions with code that no code of another calls: where values enter from outside. An operation on a
    * state is no entry: only programs call it.
    */
  def entries(t: Theory): List[SymbolName] =
    val called = t.code.attached.values.toList.flatMap(a => a.code match
      case Code.Tested(_, cs) => cs
      case c                  => c.proven.toList.flatMap(d => Callees.calledBy(t, d)))
    t.code.attached.keys.toList.filterNot(s => called.contains(s) || t.vocabulary.modelOf(s).nonEmpty)

  private def reached(m: StateModel): List[Premise] =
    List(Premise.OnlyCodeChanges(m.name), Premise.Atomic(m.name), Premise.Initially(m.name))

  /** The models of the operations the programs a claim is checked against call. */
  private def runs(t: Theory, id: NodeId): List[StateModel] =
    Callees.of(t, id).toList.flatMap(_.calls.operations).flatMap(t.vocabulary.modelOf).distinct

  /** What `ty`s from outside meet, when values from outside can hold one. */
  private def passed(t: Theory, ty: Ty): List[Premise] =
    val outside = entries(t).flatMap(inputs(t, _)) ++ provided(t)
    Option.when(outside.exists(Guards.applies(t, ty, _)))(Premise.FromOutside(ty)).toList

  /** What values from outside meet, of each type an assumption of `always` is about whose guard the node carries:
    * on what it quantifies over (a world: the stores it reads, `Reads`), and on the inputs and worlds of what its
    * `cover_` and `made_` are asked of.
    */
  private def guarded(t: Theory, n: Node): List[Premise] =
    val values = (Reads.quantified(n) ++ asked(t, n)).filter(_ != Ty.World)
    val stores = Option.when(Reads.quantified(n).contains(Ty.World))(Reads.models(t, n.id)).toList.flatten ++
      worlds(t, n)
    t.nodes.map(_.node).filter(a => a.id != n.id && a.statement.kind == NodeKind.Assumption)
      .flatMap(_.statement.range).collect {
        case r @ Range.Made(u) if values.exists(Guards.applies(t, u, _)) ||
            Scope.models(t, r).exists(m => stores.contains(m.name)) => Premise.FromOutside(u)
      }

  /** The inputs of what an `always`'s `cover_` and `made_` are asked of. */
  private def asked(t: Theory, n: Node): List[Ty] = n.statement.range.toList.flatMap { r =>
    Scope.of(t, n.id).flatMap(inputs(t, _)) ++ Scope.modelMakers(t, r).flatMap((_, sig) => sig.params.map(_._2))
  }

  /** The stores of the worlds what an `always`'s `cover_` and `made_` are asked of run from. */
  private def worlds(t: Theory, n: Node): List[ModelName] = n.statement.range.toList.flatMap { r =>
    Scope.of(t, n.id).filter(program(t, _)).flatMap(Reads.ofProgram(t, _)) ++
      Scope.modelMakers(t, r).map((m, _) => m.name)
  }

  private def program(t: Theory, op: SymbolName): Boolean =
    t.code.attached.get(op).exists(_.code match
      case Code.ProvenFlow(_) => true
      case _                  => false)

  /** The types of the values provided where the code runs. */
  private def provided(t: Theory): List[Ty] = t.code.attached.toList.collect {
    case (s, a) if a.code == Code.Provided => t.vocabulary.symbol(s).map(_.ty)
  }.flatten.collect { case SymbolType.Typed(ty) => ty }

  /** A Definition's inputs, by type. */
  private def inputs(t: Theory, d: SymbolName): List[Ty] = t.vocabulary.symbol(d).map(_.ty).toList.flatMap {
    case SymbolType.Typed(Ty.FnOf(ins, _)) => ins
    case _                                 => Nil
  }

  /** The operations on a state a program calls, through the defines it calls. */
  private def steps(t: Theory, d: DefName): List[SymbolName] =
    t.vocabulary.closure(List(d)).flatMap(x => Exprs.all(x.lambda.body)).collect { case Expr.Do(p, _) => p }
      .flatMap(Progs.operations).distinct

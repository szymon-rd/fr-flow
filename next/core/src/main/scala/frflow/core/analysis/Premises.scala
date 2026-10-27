package frflow.core.analysis

import frflow.core.code.Code
import frflow.core.expr.{Expr, Exprs, Prog, Progs, Quantifier}
import frflow.core.name.{BoundaryName, DefName, ModelName, NodeId, OpName, SymbolName}
import frflow.core.spec.{Node, NodeKind, Range}
import frflow.core.ty.Ty
import frflow.core.vocab.{StateModel, SymbolType}
import frflow.core.Theory

/** What about the world outside a statement's check rests on (owner §16, §17, §21), derived from the statement and
  * the code, each to be listed by the statement's `.assuming` (owner §15: the one mechanism; `Validate` checks the
  * list, `PremiseMissing`, `PremiseNotNeeded`):
  * - a claim about a program's runs on a store: the store behaves as its model, changed one run at a time;
  * - an `always(stored)`: those, what the state it starts in meets, and which programs write it (the rule: every
  *   start state meets it, each run of a writer keeps it, so every state reached does);
  * - an `always[T]`: the store facts of every store whose state holds a `T`, and that each store whose operations
  *   make a `T` behaves as its model (`made_<op>` is proven of the model);
  * - and, of every claim, what values from outside meet: each assumption of `always[U]` whose guard the claim's Lean
  *   form or its `made_`/`cover_` obligations carry (on a variable it quantifies over, a world, or an input of a
  *   maker or program it is asked of; `Guards.applies` decides, as it does for the guards Lean states). An
  *   `always[T]` claim also rests on what `T`s from outside meet when an entry Definition's input or a value
  *   provided where the code runs can hold one, whether or not an assumption says it: no covered code makes those.
  */
object Premises:
  def of(t: Theory, id: NodeId): List[Premise] =
    t.node(id).filter(_.statement.kind == NodeKind.Claim).toList.flatMap(n => n.statement.range.toList.flatMap {
      case Range.Possible     => runs(t, id).flatMap(m => List(Premise.BehavesAs(m), Premise.OneRunAtATime(m)))
      case Range.Reached(ms)  => ms.flatMap(reached)
      case r @ Range.Made(ty) => passed(t, ty) ++ Scope.models(t, r).map(_.name).flatMap(reached) ++
          Scope.modelMakers(t, r).map((m, _) => Premise.BehavesAs(m.name))
    } ++ guarded(t, n)).distinct

  /** The programs whose proven code writes `m`'s state, through its boundary. */
  def writers(t: Theory, m: StateModel): List[SymbolName] =
    val writing = m.ops.filter(op => Progs.all(op.steps).exists {
      case Prog.Write(_, _) | Prog.Modify(_, _, _) => true
      case _                                       => false
    }).map(_.op).toSet
    t.code.attached.toList.collect {
      case (s, a) if (a.code match { case Code.ProvenFlow(f) => steps(t, f); case _ => Nil })
          .exists((b, op) => b == m.boundary && writing(op)) => s
    }

  /** The Definitions with code that no code of another calls: where values enter from outside. */
  def entries(t: Theory): List[SymbolName] =
    val called = t.code.attached.values.toList.flatMap(a => a.code match
      case Code.Tested(_, cs) => cs
      case c                  => c.proven.toList.flatMap(d => Callees.calledBy(t, d)))
    t.code.attached.keys.toList.filterNot(called.contains)

  private def reached(m: ModelName): List[Premise] =
    List(Premise.BehavesAs(m), Premise.OneRunAtATime(m), Premise.Initially(m), Premise.WrittenOnlyBy(m))

  /** The models of the stores the programs a claim is checked against call. */
  private def runs(t: Theory, id: NodeId): List[ModelName] =
    Callees.of(t, id).toList.flatMap(_.calls.boundaries).flatMap(b => t.vocabulary.models.filter(_.boundary == b))
      .map(_.name)

  /** What `ty`s from outside meet, when values from outside can hold one. */
  private def passed(t: Theory, ty: Ty): List[Premise] =
    val outside = entries(t).flatMap(inputs(t, _)) ++ provided(t)
    Option.when(outside.exists(Guards.applies(t, ty, _)))(Premise.FromOutside(ty)).toList

  /** What values from outside meet, of each type an assumption of `always` is about whose guard the node carries:
    * on what it quantifies over, and on the inputs and worlds of what its `cover_` and `made_` are asked of.
    */
  private def guarded(t: Theory, n: Node): List[Premise] =
    val carried = quantified(n) ++ asked(t, n)
    t.nodes.map(_.node).filter(a => a.id != n.id && a.statement.kind == NodeKind.Assumption)
      .flatMap(_.statement.range).collect {
        case r @ Range.Made(u) if carried.exists(x => Guards.applies(t, u, x) ||
            (x == Ty.World && Scope.models(t, r).nonEmpty)) => Premise.FromOutside(u)
      }

  /** The types of the variables a statement's formula quantifies over (`Guarded` guards each). */
  private def quantified(n: Node): List[Ty] = n.statement.said.toList.flatMap(f => Exprs.all(f.value).collect {
    case Expr.Quant(Quantifier.Forall | Quantifier.Exists, xs, _) => xs.map(_.ty)
  }.flatten)

  /** The inputs of what an `always`'s `cover_` and `made_` are asked of, and the worlds they run from. */
  private def asked(t: Theory, n: Node): List[Ty] = n.statement.range.toList.flatMap { r =>
    Scope.of(t, n.id).flatMap(op => inputs(t, op) ++ Option.when(program(t, op))(Ty.World)) ++
      Scope.modelMakers(t, r).flatMap((_, sig) => sig.params.map(_._2) :+ Ty.World)
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

  /** The boundary operations a program calls, through the defines it calls. */
  private def steps(t: Theory, d: DefName): List[(BoundaryName, OpName)] =
    t.vocabulary.closure(List(d)).flatMap(x => Exprs.all(x.lambda.body)).collect { case Expr.Do(p, _) => p }
      .flatMap(Progs.all).collect { case Prog.Call(b, op, _, _) => b -> op }

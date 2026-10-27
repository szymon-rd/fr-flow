package frflow.core.analysis

import frflow.core.code.Code
import frflow.core.expr.{Expr, Exprs, Prog, Progs}
import frflow.core.name.{BoundaryName, DefName, ModelName, NodeId, OpName, SymbolName}
import frflow.core.spec.{NodeKind, Range}
import frflow.core.ty.Ty
import frflow.core.vocab.{StateModel, SymbolType}
import frflow.core.Theory

/** The facts about the world outside a statement's check rests on (owner §16, §17), derived from the statement and
  * the code, each to be listed by the statement's `.assuming` (owner §15: the one mechanism; `Validate` checks the
  * list, `PremiseMissing`, `PremiseNotNeeded`):
  * - a claim about a program's runs on a store: the store behaves as its model, changed one run at a time;
  * - an `always(stored)`: those, what the state it starts in meets, and which programs write it (the rule: every
  *   start state meets it, each run of a writer keeps it, so every state reached does);
  * - an `always[T]`: what values from outside meet (owner §21), the store facts of every store whose state holds a
  *   `T`, and that each store whose operations make a `T` behaves as its model (`made_<op>` is proven of the model).
  *   Values from outside are the inputs of the entry Definitions and the values provided where the code runs. When
  *   one can hold a `T`, its `T`s are made by no covered code, so what they meet must be assumed: an assumption of
  *   `always[T]`. When the Definitions the claim
  *   must hold in take inputs from outside of a type an assumption of `always` is about, the code makes its `T`s
  *   from those values under that assumption, and the claim rests on it too. Covered code that makes a `T` is still
  *   held to `made_<maker>` and `cover_<op>`, so an assumption never stands for what the code makes.
  */
object Premises:
  def of(t: Theory, id: NodeId): List[Premise] =
    t.node(id).filter(_.statement.kind == NodeKind.Claim).flatMap(_.statement.range).toList.flatMap {
      case Range.Possible     => runs(t, id).flatMap(m => List(Premise.BehavesAs(m), Premise.OneRunAtATime(m)))
      case Range.Reached(ms)  => ms.flatMap(reached)
      case r @ Range.Made(ty) =>
        fromOutside(t, ty, Scope.of(t, id)) ++ Scope.models(t, r).map(_.name).flatMap(reached) ++
          Scope.modelMakers(t, r).map((m, _) => Premise.BehavesAs(m.name))
    }.distinct

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

  /** What values from outside an `always[T]` rests on: the `T`s the outside passes in, and the values from outside
    * the code makes its `T`s from, of each type an assumption of `always` is about.
    */
  private def fromOutside(t: Theory, ty: Ty, scope: List[SymbolName]): List[Premise] =
    val outside = entries(t).flatMap(inputs(t, _)) ++ provided(t)
    val passed = Option.when(outside.exists(Scope.holds(t, ty, _)))(ty).toList
    val madeFrom = scope.flatMap(inputs(t, _)).map(element).filter(u =>
      u != ty && outside.map(element).contains(u) && Outsides.alwaysOf(t, u).nonEmpty)
    (passed ++ madeFrom).distinct.map(Premise.FromOutside(_))

  /** The types of the values provided where the code runs. */
  private def provided(t: Theory): List[Ty] = t.code.attached.toList.collect {
    case (s, a) if a.code == Code.Provided => t.vocabulary.symbol(s).map(_.ty)
  }.flatten.collect { case SymbolType.Typed(ty) => ty }

  /** A Definition's inputs, by type. */
  private def inputs(t: Theory, d: SymbolName): List[Ty] = t.vocabulary.symbol(d).map(_.ty).toList.flatMap {
    case SymbolType.Typed(Ty.FnOf(ins, _)) => ins
    case _                                 => Nil
  }

  /** The type of a list's elements, or the type itself. */
  private def element(ty: Ty): Ty = ty match
    case Ty.ListOf(x) => x
    case x            => x

  /** The boundary operations a program calls, through the defines it calls. */
  private def steps(t: Theory, d: DefName): List[(BoundaryName, OpName)] =
    t.vocabulary.closure(List(d)).flatMap(x => Exprs.all(x.lambda.body)).collect { case Expr.Do(p, _) => p }
      .flatMap(Progs.all).collect { case Prog.Call(b, op, _, _) => b -> op }

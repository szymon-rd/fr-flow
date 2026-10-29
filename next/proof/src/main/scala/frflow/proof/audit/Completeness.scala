package frflow.proof.audit

import frflow.core.analysis.{Resolve, Resolved}
import frflow.core.code.Code
import frflow.core.expr.{Expr, Exprs, Prog, Progs}
import frflow.core.name.{DefName, LeanNames, ModelName, NodeId, SymbolName, TypeName}
import frflow.core.spec.{NodeKind, Range}
import frflow.core.ty.Ty
import frflow.core.vocab.{SymbolType, ValueKind}
import frflow.proof.layout.{Layout, NodePart}
import frflow.proof.lean.ast.LeanModule

/** An oracle of soundness, computed apart from the obligations' own selection (`Required`, `Made`, `Scope`,
  * `Guards`, `CallingCode`, `Commutation`), from the theory read afresh and the modules' syntax (`Assumed`).
  *
  * Every rule of `always` some generated statement takes as a hypothesis is discharged: of a rule about a store's
  * state (`always(stored)`, or `always[T]` where the state holds a `T`), `start_<rule>` and `cover_<p>` of each
  * proven program `p` calling an operation that changes the state; of `always[T]`, `made_<d>` of each proven
  * Definition whose result holds a `T` (a define's, or a program's run's), `made_<op>` of each operation whose result
  * does, and `made_<code>_call_<i>` at each call `i` of code not proven that proven code hands a `T`.
  *
  * Every stated node is asked what its place asks: with parts, `complete` (or `impl`); a claim of proven code (but
  * one saying what a Declaration is, at the bottom), `impl`, and `commute_<i>` of each parallel step of the proven
  * programs it mentions.
  */
object Completeness:
  /** A discharge a node needs and the modules do not state. */
  final case class Missing(node: NodeId, obligation: String, why: String)

  def of(r: Resolved, modules: List[LeanModule]): List[Missing] = rules(r, modules) ++ nodes(r, modules)

  private def rules(r: Resolved, modules: List[LeanModule]): List[Missing] =
    val t = r.theory
    val taken = Assumed.taken(modules).collect { case List(k, rule) if k.text == t.name.value => rule.text }.toSet
    val rules = t.nodes.map(_.node).filter(n => n.statement.rule && taken(LeanNames.define(n.id.value)))
    rules.flatMap(n => n.statement.range.toList.flatMap(needs(r, _, n.id))).distinct
      .filterNot((rule, name, _) => stated(modules, Layout(t.name), rule, name).contains(name)).map(Missing.apply)

  private def nodes(r: Resolved, modules: List[LeanModule]): List[Missing] =
    val t = r.theory
    t.refinement.nodes.filter(_.statement.stated).flatMap { n =>
      val have = stated(modules, Layout(t.name), n.id, "")
      val mentioned = Resolve.mentions(t, n.id).symbols.toSet
      val code = proven(r).filter((s, _) => mentioned(s))
      val parts = t.refinement.parts(n.id).nonEmpty
      val saysWhat = !parts && mentioned.exists(s => t.vocabulary.symbol(s).exists(_.kind == ValueKind.Declaration))
      val impl = n.statement.kind == NodeKind.Claim && code.nonEmpty && !saysWhat
      val flows = if impl then code.collect { case (_, Code.ProvenFlow(f)) => f }.distinct else Nil
      val parallel = flows.flatMap(program(r, _)).flatMap(Progs.all).count {
        case Prog.Par(_, _, _, _) | Prog.ParEach(_, _, _, _) => true
        case _                                             => false
      }
      (Option.when(impl)("impl" -> "it is claimed of proven code").toList ++
        Option.when(parts && !impl && !have.contains("impl"))("complete" -> "it has parts").toList ++
        (0 until parallel).map(i => s"commute_$i" -> s"parallel step ${i + 1} of its proven programs"))
        .filterNot((name, _) => have.contains(name)).map((name, why) => Missing(n.id, name, why))
    }

  /** Each discharge a rule needs: its obligation's name, and why. */
  private def needs(r: Resolved, range: Range, rule: NodeId): List[(NodeId, String, String)] =
    val t = r.theory
    val ty = range match
      case Range.Made(x) => Some(x)
      case _             => None
    val stores = range match
      case Range.Reached(ms) => ms
      case Range.Made(x)     => t.vocabulary.models.filter(m => holds(r, x)(m.state)).map(_.name)
      case Range.Possible    => Nil
    val writers = proven(r).collect { case (d, Code.ProvenFlow(f)) if program(r, f).exists(changes(r, stores)) => d }
    val starts = Option.when(stores.nonEmpty)((rule, s"start_${rule.value}", "the store's start meets it")).toList
    val covers = writers.map(w => (rule, s"cover_${w.value}", s"${w.value} changes a store it is about"))
    starts ++ covers ++ ty.toList.flatMap(made(r, rule, _))

  private def made(r: Resolved, rule: NodeId, ty: Ty): List[(NodeId, String, String)] =
    val t = r.theory
    val results = proven(r).flatMap((d, c) => resultOf(r, d, c).filter(holds(r, ty)).map(_ => d))
      .map(d => (rule, s"made_${d.value}", s"${d.value}'s proven code makes it"))
    val ops = t.vocabulary.models.flatMap(_.ops).filter(o => holds(r, ty)(o.result))
      .map(o => (rule, s"made_${o.op.value}", s"the operation ${o.op.value} makes it"))
    val calls = proven(r).flatMap((_, c) => c.proven.toList).distinct.flatMap(d => plainCalls(r, d).zipWithIndex
      .collect { case (tys, i) if tys.exists(holds(r, ty)) =>
        (rule, s"made_${LeanNames.call(d, i)}", s"${d.value} hands one to code not proven at call ${i + 1}")
      })
    results ++ ops ++ calls

  /** The Definitions with proven code, and their code. */
  private def proven(r: Resolved): List[(SymbolName, Code)] = r.theory.code.attached.toList.sortBy(_._1.value)
    .map((d, a) => d -> a.code).filter(_._2.proven.nonEmpty)

  /** What a proven Definition's value holds: a define's result, a program's run's result. */
  private def resultOf(r: Resolved, d: SymbolName, c: Code): Option[Ty] =
    r.theory.vocabulary.symbol(d).map(_.ty).collect { case SymbolType.Typed(ty) => Ty.resultOf(ty) }.map(res =>
      c match
        case Code.ProvenFlow(_) => Ty.yields(res)
        case _                  => res)

  /** A program's steps, as recorded. */
  private def program(r: Resolved, f: DefName): List[Prog[Expr]] =
    r.theory.vocabulary.define(f).toList.map(_.lambda.body).collect { case Expr.Do(p, _) => p }

  /** The program calls an operation whose meaning writes one of `stores`. */
  private def changes(r: Resolved, stores: List[ModelName])(p: Prog[Expr]): Boolean =
    val writing = r.theory.vocabulary.models.flatMap(m => m.ops.filter(o => Progs.all(o.steps).exists {
      case Prog.Write(s, _)     => stores.contains(s) && s == m.name
      case Prog.Modify(s, _, _) => stores.contains(s) && s == m.name
      case _                    => false
    }).map(_.op)).toSet
    Progs.all(p).exists {
      case Prog.Call(op, _, _) => writing(op)
      case _                   => false
    }

  /** The calls of code not proven (plain Scala, an operation on a state) in proven code, in the order it makes
    * them (a call's arguments' before it, a step's terms' before the steps after it), through the defines it calls
    * (each read where it is called): each call's arguments' types.
    */
  private def plainCalls(r: Resolved, d: DefName): List[List[Ty]] =
    val t = r.theory
    def plain(s: SymbolName) = t.code.attached.get(s).exists(_.code.proven.isEmpty)
    def in(e: Expr, seen: Set[DefName]): List[List[Ty]] = (e match
      case Expr.Do(p, _) => steps(p, seen)
      case _             => Exprs.children(e).flatMap(in(_, seen))) ++ (e match
      case Expr.Apply(Expr.Sym(s, _), as, _) if plain(s) => List(as.map(Exprs.typeOf))
      case Expr.Call(c, _, _) if !seen(c)              =>
        t.vocabulary.define(c).toList.flatMap(x => in(x.lambda.body, seen + c))
      case _                                           => Nil)
    def steps(p: Prog[Expr], seen: Set[DefName]): List[List[Ty]] =
      own(p).flatMap(in(_, seen)) ++ (p match
        case Prog.Call(op, as, _) if plain(op) => List(as.map(Exprs.typeOf))
        case _                                 => Nil) ++ Progs.children(p).flatMap(steps(_, seen))
    t.vocabulary.define(d).toList.flatMap(x => in(x.lambda.body, Set(d)))

  /** A step's own terms, not its sub-steps'. */
  private def own(p: Prog[Expr]): List[Expr] = p match
    case Prog.Pure(t)                    => List(t)
    case Prog.Call(_, as, _)             => as
    case Prog.Let(_, v, _)               => List(v)
    case Prog.Loop(xs, _, _)             => List(xs)
    case Prog.Collect(xs, _, _)          => List(xs)
    case Prog.Accumulate(xs, z, _, _, _) => List(xs, z)
    case Prog.Branch(c, _, _)            => List(c)
    case Prog.Write(_, s)                => List(s)
    case Prog.Modify(_, _, s)            => List(s)
    case Prog.Raise(e)                   => List(e)
    case Prog.ParEach(xs, _, _, _)       => List(xs)
    case _                               => Nil

  /** Whether a value of `x` holds a `ty`: itself, an element of a list or an option, a side, a component, a field. */
  private def holds(r: Resolved, ty: Ty)(x: Ty): Boolean =
    def go(x: Ty, seen: Set[TypeName]): Boolean = x == ty || (x match
      case Ty.ListOf(a)           => go(a, seen)
      case Ty.OptionOf(a)         => go(a, seen)
      case Ty.EitherOf(e, a)      => go(e, seen) || go(a, seen)
      case Ty.TupleOf(as)         => as.exists(go(_, seen))
      case Ty.Data(n) if !seen(n) => r.theory.vocabulary.dataType(n).exists(_.fieldTypes.exists(go(_, seen + n)))
      case _                      => false)
    go(x, Set.empty)

  /** What the modules state where the obligation would be: the node's `Spec`, or the whole theory's for a `start_`. */
  private def stated(modules: List[LeanModule], l: Layout, node: NodeId, name: String): List[String] =
    Assumed.defs(modules.filter(_.name == (if name.startsWith("start_") then l.wholeSpec
      else l.ofNode(node, NodePart.Spec))))

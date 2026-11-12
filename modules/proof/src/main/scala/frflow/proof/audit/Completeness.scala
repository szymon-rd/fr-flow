package frflow.proof.audit

import frflow.core.analysis.resolution.{Resolve, Resolved}
import frflow.core.code.Code
import frflow.core.expr.{Expr, Exprs}
import frflow.core.name.{DefName, LeanNames, NodeId, SymbolName, TypeName}
import frflow.core.spec.{NodeKind, Range}
import frflow.core.ty.Ty
import frflow.core.vocab.{SymbolType, ValueKind}
import frflow.proof.layout.{Layout, NodePart}
import frflow.proof.lean.ast.LeanModule

/** An oracle of soundness, computed apart from the obligations' own selection (`Required`, `Made`, `Scope`,
  * `Guards`, `CallingCode`), from the theory read afresh and the modules' syntax (`Assumed`).
  *
  * Every rule of `always[T]` some generated statement takes as a hypothesis is discharged: `made_<d>` of each proven
  * Definition whose result holds a `T`, and `made_<code>_call_<i>` at each call `i` of code not proven that proven
  * code hands a `T`.
  *
  * Every stated node is asked what its place asks: with parts, `complete` (or `impl`); a claim of proven code (but
  * one saying what a Declaration is, at the bottom), `impl`.
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
      .filterNot((rule, name, _) => stated(modules, Layout(t.name), rule).contains(name)).map(Missing.apply)

  private def nodes(r: Resolved, modules: List[LeanModule]): List[Missing] =
    val t = r.theory
    t.refinement.nodes.filter(_.statement.stated).flatMap { n =>
      val have = stated(modules, Layout(t.name), n.id)
      val mentioned = Resolve.mentions(t, n.id).symbols.toSet
      val code = proven(r).filter((s, _) => mentioned(s))
      val parts = t.refinement.parts(n.id).nonEmpty
      val saysWhat = !parts && mentioned.exists(s => t.vocabulary.symbol(s).exists(_.kind == ValueKind.Declaration))
      val claim = n.statement.kind == NodeKind.Claim && !saysWhat
      val impl = claim && code.nonEmpty
      (Option.when(impl)("impl" -> "it is claimed of proven code").toList ++
        Option.when(parts && !impl && !have.contains("impl"))("complete" -> "it has parts").toList)
        .filterNot((name, _) => have.contains(name)).map((name, why) => Missing(n.id, name, why))
    }

  /** Each discharge a rule needs: its obligation's name, and why. */
  private def needs(r: Resolved, range: Range, rule: NodeId): List[(NodeId, String, String)] = range match
    case Range.Made(ty) => made(r, rule, ty)
    case Range.Possible => Nil

  private def made(r: Resolved, rule: NodeId, ty: Ty): List[(NodeId, String, String)] =
    val results = proven(r).flatMap((d, _) => resultOf(r, d).filter(holds(r, ty)).map(_ => d))
      .map(d => (rule, s"made_${d.value}", s"${d.value}'s proven code makes it"))
    val calls = proven(r).flatMap((_, c) => c.proven.toList).distinct.flatMap(d => plainCalls(r, d).zipWithIndex
      .collect { case (tys, i) if tys.exists(holds(r, ty)) =>
        (rule, s"made_${LeanNames.call(d, i)}", s"${d.value} hands one to code not proven at call ${i + 1}")
      })
    results ++ calls

  /** The Definitions with proven code, and their code. */
  private def proven(r: Resolved): List[(SymbolName, Code)] = r.theory.code.attached.toList.sortBy(_._1.value)
    .map((d, a) => d -> a.code).filter(_._2.proven.nonEmpty)

  /** What a proven Definition's value holds: a define's result. */
  private def resultOf(r: Resolved, d: SymbolName): Option[Ty] =
    r.theory.vocabulary.symbol(d).map(_.ty).collect { case SymbolType.Typed(ty) => Ty.resultOf(ty) }

  /** The calls of code not proven (plain Scala) in proven code, in the order it makes them (a call's arguments'
    * before it), through the defines it calls (each read where it is called): each call's arguments' types.
    */
  private def plainCalls(r: Resolved, d: DefName): List[List[Ty]] =
    val t = r.theory
    def plain(s: SymbolName) = t.code.attached.get(s).exists(_.code.proven.isEmpty)
    def in(e: Expr, seen: Set[DefName]): List[List[Ty]] = Exprs.children(e).flatMap(in(_, seen)) ++ (e match
      case Expr.Apply(Expr.Sym(s, _), as, _) if plain(s) => List(as.map(Exprs.typeOf))
      case Expr.Call(c, _, _) if !seen(c)              =>
        t.vocabulary.define(c).toList.flatMap(x => in(x.lambda.body, seen + c))
      case _                                           => Nil)
    t.vocabulary.define(d).toList.flatMap(x => in(x.lambda.body, Set(d)))

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

  /** What the modules state where the obligation would be: the node's `Spec`. */
  private def stated(modules: List[LeanModule], l: Layout, node: NodeId): List[String] =
    Assumed.defs(modules.filter(_.name == l.ofNode(node, NodePart.Spec)))

package frflow.proof.obligation

import frflow.core.analysis.Resolved
import frflow.core.code.Code
import frflow.core.expr.{Expr, Exprs, Prog, Progs}
import frflow.core.name.{DefName, LeanNames, ModelName, NodeId, SymbolName, TypeName}
import frflow.core.spec.Range
import frflow.core.ty.Ty
import frflow.core.vocab.SymbolType
import frflow.proof.layout.{Layout, NodePart}
import frflow.proof.lean.ast.*

/** An oracle of soundness, computed apart from the obligations' own selection (`Required`, `Made`, `Scope`,
  * `Guards`, `CallingCode`): every rule of `always` some generated statement takes as a hypothesis is discharged.
  * From the modules, the rules taken (a rule's define applied where a statement assumes it, left of `→` or as a
  * hypothesis binder) and the obligations stated (`Obl.<name>` in each rule's `Spec`, `start_<rule>` in the whole
  * theory's); from the theory read afresh, what each rule needs: of a rule about a store's state (`always(stored)`,
  * or `always[T]` where the state holds a `T`), `start_<rule>` and `cover_<p>` of each proven program `p` calling an
  * operation that changes the state; of `always[T]`, `made_<d>` of each proven Definition whose result holds a `T`
  * (a define's, or a program's run's), `made_<op>` of each operation whose result does, and as many
  * `made_<code>_call_<i>` as the proven code has calls of code not proven handed a `T`.
  */
object Completeness:
  /** A discharge a rule taken as a hypothesis needs and the modules do not state. */
  final case class Missing(rule: NodeId, obligation: String, why: String)

  def of(r: Resolved, modules: List[LeanModule]): List[Missing] =
    val t = r.theory
    val kb = t.name.value
    val decls = modules.flatMap(_.decls).flatMap(flat)
    val taken = decls.flatMap(statements).flatMap(e => assumed(e, negative = false)).flatMap {
      case List(k, rule) if k.text == kb => Some(rule.text)
      case _                             => None
    }.toSet
    val rules = t.nodes.map(_.node).filter(n => n.statement.rule && taken(LeanNames.define(n.id.value)))
    val (calls, others) = rules.flatMap(n => n.statement.range.toList.flatMap(needs(r, _, n.id))).distinct
      .partition(_._2.endsWith("_call_"))
    def names(rule: NodeId, name: String) = stated(modules, Layout(t.name), rule, name)
    others.filterNot((rule, name, _) => names(rule, name).contains(name)).map(Missing.apply) ++
      calls.groupBy(c => (c._1, c._2)).toList.sortBy(_._1.toString).flatMap { case ((rule, prefix), cs) =>
        val have = names(rule, prefix).count(_.startsWith(prefix))
        Option.when(have < cs.size)(Missing(rule, s"$prefix<i>", s"${cs.head._3}: ${cs.size} calls, $have stated"))
      }

  /** Each discharge a rule needs: its obligation's name (a `made_<code>_call_` prefix asked as often as it is
    * listed), and why.
    */
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
    val calls = proven(r).flatMap((_, c) => c.proven.toList).flatMap(d => plainCalls(r, d).filter(_.exists(holds(r,
      ty))).map(_ => (rule, s"made_${d.value}_call_", s"${d.value} hands one to code not proven")))
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

  /** The calls of code not proven (plain Scala, an operation on a state) in proven code, through the defines it
    * calls: each call's arguments' types.
    */
  private def plainCalls(r: Resolved, d: DefName): List[List[Ty]] =
    val t = r.theory
    def plain(s: SymbolName) = t.code.attached.get(s).exists(_.code.proven.isEmpty)
    def in(e: Expr, seen: Set[DefName]): List[List[Ty]] = Exprs.all(e).flatMap {
      case Expr.Apply(Expr.Sym(s, _), as, _) if plain(s) => List(as.map(Exprs.typeOf))
      case Expr.Call(c, _, _) if !seen(c)              => t.vocabulary.define(c).toList.flatMap(x =>
          in(x.lambda.body, seen + c))
      case Expr.Do(p, _)                               => Progs.all(p).collect {
          case Prog.Call(op, as, _) if plain(op) => as.map(Exprs.typeOf)
        }
      case _                                           => Nil
    }
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

  /** What the modules state where the obligation would be: the rule's `Spec`, or the whole theory's for a `start_`. */
  private def stated(modules: List[LeanModule], l: Layout, rule: NodeId, name: String): List[String] =
    val in = if name.startsWith("start_") then modules.filter(_.name == l.wholeSpec)
      else modules.filter(_.name == l.ofNode(rule, NodePart.Spec))
    in.flatMap(_.decls).flatMap(flat).collect { case Decl.Def(_, n, _, _, _) => n.text }

  private def flat(d: Decl): List[Decl] = d match
    case Decl.Documented(_, x)  => flat(x)
    case Decl.Namespace(_, ds)  => ds.flatMap(flat)
    case Decl.Budgeted(_, x)    => flat(x)
    case other                  => List(other)

  private def statements(d: Decl): List[LExpr] = d match
    case Decl.Def(_, _, ps, ty, body)    => hypotheses(ps) ++ List(ty, body)
    case Decl.Theorem(_, _, ps, s, _, _) => hypotheses(ps) :+ s
    case _                               => Nil

  /** A declaration's parameters that are hypotheses, each read as assumed (as the left of `→`). */
  private def hypotheses(ps: List[LBinder]): List[LExpr] = ps.collect { case LBinder.Explicit(_, t) =>
    LExpr.Infix(LOp.Arrow, t, LExpr.Name(Names.builtin("True"))) }

  /** The constants applied where `e` assumes them: left of `→`, a hypothesis binder's type, under a `¬` turned. */
  private def assumed(e: LExpr, negative: Boolean): List[List[LeanName]] = e match
    case LExpr.Const(p) if negative               => List(p)
    case LExpr.App(f, as)                          => (f :: as).flatMap(assumed(_, negative))
    case LExpr.Infix(LOp.Arrow, a, b)              => assumed(a, !negative) ++ assumed(b, negative)
    case LExpr.Infix(_, a, b)                      => assumed(a, negative) ++ assumed(b, negative)
    case LExpr.Prefix(_, a)                        => assumed(a, !negative)
    case LExpr.Paren(i)                            => assumed(i, negative)
    case LExpr.Forall(ps, b)                       => ps.flatMap(binder(_, !negative)) ++ assumed(b, negative)
    case LExpr.Exists(ps, b)                       => ps.flatMap(binder(_, negative)) ++ assumed(b, negative)
    case LExpr.Fun(_, b)                           => assumed(b, negative)
    case LExpr.Match(on, arms)                     =>
      assumed(on, negative) ++ arms.flatMap(a => assumed(a._2, negative))
    case LExpr.If(c, a, b)                         => assumed(c, true) ++ assumed(c, false) ++ assumed(a, negative) ++
        assumed(b, negative)
    case LExpr.Let(_, _, v, b)                     => assumed(v, negative) ++ assumed(b, negative)
    case LExpr.Typed(x, _)                         => assumed(x, negative)
    case _                                         => Nil

  private def binder(b: LBinder, negative: Boolean): List[List[LeanName]] = b match
    case LBinder.Explicit(_, t) => assumed(t, negative)
    case LBinder.Member(_, in)  => assumed(in, negative)
    case _                      => Nil

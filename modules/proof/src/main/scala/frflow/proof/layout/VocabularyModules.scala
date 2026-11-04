package frflow.proof.layout

import cats.syntax.all.*
import frflow.core.expr.{Expr, Prog, Progs}
import frflow.core.analysis.Waits
import frflow.core.analysis.outside.Guards
import frflow.core.name.DefName
import frflow.core.spec.{Form, Range}
import frflow.core.term.interpret.{Guard, Guarded}
import frflow.core.ty.{DataType, Ty}
import frflow.core.vocab.{Define, DefineForm}
import frflow.proof.lean.ast.*
import frflow.proof.lean.lower.{Atoms, LowerEnv, LowerModels, LowerFaults, LowerProg, LowerType, Naming}
import frflow.proof.lean.term.Printed

/** The modules of the vocabulary: `Types` (the domain's types, each after those its fields name), a `Def_` module per
  * define (a change to one rebuilds only what uses it), `Models` (the classes, models and world: a world with no
  * model when there is none, what a program's runs are between), and `Domain`,
  * importing every define's.
  */
object VocabularyModules:
  import Atoms.name

  def of(r: frflow.core.analysis.Resolved): List[LeanModule] = of(Lowering(r, frflow.proof.terms.TermTable.of(r)))

  def of(l: Lowering): List[LeanModule] =
    val v = l.resolved.theory.vocabulary
    (types(l) :: models(l) :: v.defines.map(define(l, _))) ++ v.defines.filter(d => l.ruleSide.twice(d.name))
      .map(guardedTwin(l, _)) :+ domain(l)

  private def module(l: Lowering, name: ModuleName, decls: List[Decl]): LeanModule =
    Imports.onto(l, LeanModule(name, Nil, Preamble.generated, Names.path(l.kb.value), Nil, decls))

  private def types(l: Lowering): LeanModule =
    val ordered = inOrder(l.resolved.theory.vocabulary.types, Nil)
    LeanModule(l.layout.types, List(ModuleName(Names.path("FrFlow"))), Preamble.generated, Names.path(l.kb.value),
      Nil, ordered.map(typeDecl))

  /** Each type after the types its fields name. */
  private def inOrder(left: List[DataType], done: List[DataType]): List[DataType] =
    left.partition(d => d.uses.forall(u => done.exists(_.typeName == u) || !left.exists(_.typeName == u))) match
      case (Nil, rest)   => done ++ rest
      case (ready, rest) => inOrder(rest, done ++ ready)

  private def typeDecl(d: DataType): Decl = d match
    case DataType.Product(n, _, fs) =>
      Decl.Structure(Names.ident(n.value), fs.map(f => Names.ident(f.name) -> LowerType(f.ty)))
    case DataType.Sum(n, _, cs)     => Decl.Inductive(Names.ident(n.value), cs.toList.map(c =>
      Names.ident(c.name.value) -> c.fields.map(f => LBinder.Explicit(Names.ident(f.name), LowerType(f.ty)))))

  private def models(l: Lowering): LeanModule =
    val v = l.resolved.theory.vocabulary
    val lowered = LowerModels(l.env, l.naming)
    val results = v.models.flatMap(m => m.sigs.filter(_.result != Ty.Unit).map(lowered.resultOf(m, _)))
    val errors = v.defines.filter(_.form == DefineForm.Flow).flatMap(d => Ty.errorOf(d.lambda.result)).distinct
    module(l, l.layout.models, lowered.decls(v.models, errors) ++ results)

  private def domain(l: Lowering): LeanModule =
    val defines = l.resolved.theory.vocabulary.defines.map(d => l.layout.define(d.name)) ++
      l.ruleSide.twice.toList.sortBy(_.value).map(d => l.layout.define(LowerEnv.guarded(d)))
    LeanModule(l.layout.domain, l.layout.types :: defines, Preamble.generated, Names.path(l.kb.value), Nil, Nil)

  private def define(l: Lowering, d: Define): LeanModule =
    module(l, l.layout.define(d.name), List(declared(l, d), Decl.MatchEqns))

  /** A define a rule calls, as statements call it (`RuleSide`): every value rule's guard on its `forall`s, and the
    * defines it calls as statements call them.
    */
  private def guardedTwin(l: Lowering, d: Define): LeanModule = d.written.form match
    case Form.Term(t) =>
      val (bs, body) = Printed.define(l.env, l.naming)(d.lambda.params, Guarded.of(t.run, valueRules(l)))
      module(l, l.layout.define(LowerEnv.guarded(d.name)), List(Decl.Def(List(Attr.FrflowDefs),
        Names.define(LowerEnv.guarded(d.name).value), openBinders(l, d) ++ bs, LowerType(d.lambda.result), body),
        Decl.MatchEqns))
    case Form.Steps(_) => throw IllegalStateException(s"FrFlow bug: ${d.name.value}'s steps lowered twice")

  private def valueRules(l: Lowering): List[Guard] = Guards.byAlways(l.resolved.theory).collect {
    case (rule, g) if l.resolved.theory.node(rule).flatMap(_.statement.range).exists {
          case Range.Made(ty) => ty != Ty.World
          case _              => false
        } => g
  }

  /** A define as Lean is given it: a program generic in its monad, a run of one, or a term's `def`. */
  def declared(l: Lowering, written: Define): Decl =
    val d = Waits.of(l.resolved.theory.vocabulary, written)
    (d.form, d.written.form) match
      case (DefineForm.RunOf(flow), _)           =>
        LowerModels(l.env, l.naming).run(d, flow, opens(l, d).map(s => s -> l.table.typeOf(s)))
      case (DefineForm.Flow, Form.Steps(p))      => flow(l, d, p)
      case (_, Form.Term(t))                     =>
        val env = if l.ruleSide.defines(d.name) then l.env.copy(ruleSide = true) else l.env
        val (bs, body) = Printed.define(env, l.naming)(d.lambda.params, Guarded.of(t.run, guards(l, d)))
        Decl.Def(List(Attr.FrflowDefs), Names.define(d.name.value), openBinders(l, d) ++ bs,
          LowerType(d.lambda.result), body)
      case (_, Form.Steps(_))                    =>
        throw IllegalStateException(s"FrFlow bug: ${d.name.value}'s steps are not a program's")

  /** What a define's `forall`s come with, as a statement's do (semantics review, finding 5): each value rule
    * (`always[T]`) on its variable's type, but those of rules that call the define, which would be about themselves.
    * So a define read inline means what it does named. A rule's own define is the rule, guarded by none.
    */
  private def guards(l: Lowering, d: Define): List[Guard] =
    val t = l.resolved.theory
    val rules = Guards.byAlways(t).map(_._1)
    if rules.exists(r => DefName(r.value) == d.name) then Nil
    else Guards.byAlways(t).collect {
      case (rule, g) if t.node(rule).flatMap(_.statement.range).exists {
            case Range.Made(ty) => ty != Ty.World
            case _              => false
          } && !t.vocabulary.closure(List(DefName(rule.value))).exists(_.name == d.name) => g
    }

  /** A program, generic in its monad:`{m : Type → Type} [Monad m] [MonadExceptOf E m] [Bookings m] (open terms) :
    * A → m R := fun (a : A) => do …`, the monad's name taken by no symbol (`Naming.helper`).
    */
  private def flow(l: Lowering, d: Define, p: frflow.core.expr.Prog[frflow.core.term.Stated[?]]): Decl =
    val (named, m) = Naming.helper("m", Set.empty).run(l.naming).value
    val result = Ty.yields(d.lambda.result)
    val inputs = d.lambda.params
    val (bs, lines) = (inputs.traverse(x => Naming.bind(x).map(LBinder.Explicit(_, LowerType(x.ty)))),
      LowerProg(l.env, inputs.size).block(p)).tupled.runA(named).value
    val body = if bs.isEmpty then LExpr.Do(lines, 4) else LExpr.Fun(bs, LExpr.Do(lines, 4))
    Decl.Def(List(Attr.FrflowDefs), Names.define(d.name.value), monad(l, d, m) ++ openBinders(l, d),
      LowerType.declaration(inputs.map(_.ty), LExpr.App(LExpr.Name(m), List(LowerType(result)))), body)

  /** The monad a program is over: any, with the errors it raises or handles and the classes of the models whose
    * operations it calls.
    */
  private def monad(l: Lowering, d: Define, m: LeanName): List[LBinder] =
    val ir = d.lambda.body match
      case Expr.Do(q, _) => q
      case _             => throw IllegalStateException(s"FrFlow bug: ${d.name.value} is a program with no steps")
    val v = l.resolved.theory.vocabulary
    val models = Progs.operations(ir).flatMap(v.modelOf).distinct
    val errors = (Progs.errors(ir) ++ models.flatMap(_.failsWith)).distinct
    val classes = models.map(LowerModels.className)
    LBinder.Implicit(m, LExpr.Infix(LOp.Arrow, name("Type"), name("Type"))) ::
      LBinder.Instance(LExpr.App(name("Monad"), List(LExpr.Name(m)))) ::
      errors.map(e => LBinder.Instance(LExpr.App(name("MonadExceptOf"), List(LowerType(e), LExpr.Name(m))))) ++
      classes.map(c => LBinder.Instance(LExpr.App(LExpr.Name(c), List(LExpr.Name(m))))) ++
      Option.when(LowerFaults.races(ir))(LowerFaults.racesBinder(m)) ++
      Option.when(Progs.operations(ir).contains(Prog.reach))(LowerFaults.waitsBinder(m))

  private def opens(l: Lowering, d: Define) = l.table.defines.get(d.name).toList.flatMap(_.symbols)

  /** The open terms a define is over: its opaque types implicit, its symbols explicit. */
  private def openBinders(l: Lowering, d: Define): List[LBinder] =
    val sorts = l.table.defines.get(d.name).toList.flatMap(_.sorts)
    sorts.map(s => LBinder.Implicit(Names.ident(s.value), name("Type"))) ++
      opens(l, d).map(s => LBinder.Explicit(Names.ident(s.value), l.env.openType(s, l.table.typeOf(s))))

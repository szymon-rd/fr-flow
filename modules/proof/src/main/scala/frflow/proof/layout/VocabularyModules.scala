package frflow.proof.layout

import frflow.core.analysis.outside.Guards
import frflow.core.name.DefName
import frflow.core.spec.Form
import frflow.core.term.interpret.{Guard, Guarded}
import frflow.core.ty.DataType
import frflow.core.vocab.Define
import frflow.proof.lean.ast.*
import frflow.proof.lean.lower.{Atoms, LowerEnv, LowerType}
import frflow.proof.lean.term.Printed

/** The modules of the vocabulary: `Types` (the domain's types, each after those its fields name), a `Def_` module per
  * define (a change to one rebuilds only what uses it), and `Domain`, importing every define's.
  */
object VocabularyModules:
  import Atoms.name

  def of(r: frflow.core.analysis.resolution.Resolved): List[LeanModule] =
    of(Lowering(r, frflow.proof.terms.TermTable.of(r)))

  def of(l: Lowering): List[LeanModule] =
    val v = l.resolved.theory.vocabulary
    (types(l) :: v.defines.map(define(l, _))) ++ v.defines.filter(d => l.ruleSide.twice(d.name))
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

  private def valueRules(l: Lowering): List[Guard] = Guards.of(l.resolved.theory)

  /** A define as the prover is given it: a term's `def`. */
  def declared(l: Lowering, d: Define): Decl = d.written.form match
    case Form.Term(t) =>
      val env = if l.ruleSide.defines(d.name) then l.env.copy(ruleSide = true) else l.env
      val (bs, body) = Printed.define(env, l.naming)(d.lambda.params, Guarded.of(t.run, guards(l, d)))
      Decl.Def(List(Attr.FrflowDefs), Names.define(d.name.value), openBinders(l, d) ++ bs,
        LowerType(d.lambda.result), body)

  /** What a define's `forall`s come with, as a statement's do : each value rule
    * (`always[T]`) on its variable's type, but those of rules that call the define, which would be about themselves.
    * So a define read inline means what it does named. A rule's own define is the rule, guarded by none.
    */
  private def guards(l: Lowering, d: Define): List[Guard] =
    val t = l.resolved.theory
    val rules = Guards.byAlways(t).map(_._1)
    if rules.exists(r => DefName(r.value) == d.name) then Nil
    else Guards.byAlways(t).collect {
      case (rule, g) if !t.vocabulary.closure(List(DefName(rule.value))).exists(_.name == d.name) => g
    }

  private def opens(l: Lowering, d: Define) = l.table.defines.get(d.name).toList.flatMap(_.symbols)

  /** The open terms a define is over: its opaque types implicit, its symbols explicit. */
  private def openBinders(l: Lowering, d: Define): List[LBinder] =
    val sorts = l.table.defines.get(d.name).toList.flatMap(_.sorts)
    sorts.map(s => LBinder.Implicit(Names.ident(s.value), name("Type"))) ++
      opens(l, d).map(s => LBinder.Explicit(Names.ident(s.value), LowerType.binder(l.table.typeOf(s))))

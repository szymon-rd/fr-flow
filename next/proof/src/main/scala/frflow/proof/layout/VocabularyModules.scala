package frflow.proof.layout

import cats.syntax.all.*
import frflow.core.expr.{Expr, Progs}
import frflow.core.spec.Form
import frflow.core.ty.{DataType, Ty}
import frflow.core.vocab.{Define, DefineForm}
import frflow.proof.lean.ast.*
import frflow.proof.lean.lower.{Atoms, LowerModels, LowerProg, LowerType, Naming}
import frflow.proof.lean.term.Printed

/** The modules of the vocabulary: `Types` (the domain's types, each after those its fields name), a `Def_` module per
  * define (a change to one rebuilds only what uses it), `Boundaries` (the classes, models and world: a world with no
  * model when there is none, what a program's runs are between), and `Domain`,
  * importing every define's.
  */
object VocabularyModules:
  import Atoms.name

  def of(r: frflow.core.analysis.Resolved): List[LeanModule] = of(Lowering(r, frflow.proof.terms.TermTable.of(r)))

  def of(l: Lowering): List[LeanModule] =
    val v = l.resolved.theory.vocabulary
    (types(l) :: boundaries(l) :: v.defines.map(define(l, _))) :+ domain(l)

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

  private def boundaries(l: Lowering): LeanModule =
    val v = l.resolved.theory.vocabulary
    val worlds = v.models.flatMap(m => v.boundary(m.boundary).map(_ -> m))
    val models = LowerModels(l.env, l.naming)
    val results = worlds.flatMap((b, m) => b.ops.filter(_.result != Ty.Unit).map(models.resultOf(m, _)))
    val errors = v.defines.filter(_.form == DefineForm.Flow).flatMap(d => Ty.errorOf(d.lambda.result)).distinct
    module(l, l.layout.boundaries, models.decls(worlds, errors) ++ results)

  private def domain(l: Lowering): LeanModule =
    val defines = l.resolved.theory.vocabulary.defines.map(d => l.layout.define(d.name))
    LeanModule(l.layout.domain, l.layout.types :: defines, Preamble.generated, Names.path(l.kb.value), Nil, Nil)

  private def define(l: Lowering, d: Define): LeanModule =
    module(l, l.layout.define(d.name), List(declared(l, d), Decl.MatchEqns))

  private def declared(l: Lowering, d: Define): Decl = (d.form, d.written.form) match
    case (DefineForm.RunOf(flow), _)           =>
      LowerModels(l.env, l.naming).run(d, flow, opens(l, d).map(s => s -> l.table.typeOf(s)))
    case (DefineForm.Flow, Form.Steps(p))      => flow(l, d, p)
    case (_, Form.Term(t))                     =>
      val (bs, body) = Printed.define(l.env, l.naming)(d.lambda.params, t.run)
      Decl.Def(List(Attr.FrflowDefs), Names.builtin(d.name.value), openBinders(l, d) ++ bs,
        LowerType(d.lambda.result), body)
    case (_, Form.Steps(_))                    =>
      throw IllegalStateException(s"FrFlow bug: ${d.name.value}'s steps are not a program's")

  /** A program, generic in its monad: `{m : Type → Type} [Monad m] [MonadExceptOf E m] [Bookings m] (open terms) :
    * A → m R := fun (a : A) => do …`, the monad's name taken by no symbol (`Naming.helper`).
    */
  private def flow(l: Lowering, d: Define, p: frflow.core.expr.Prog[frflow.core.term.Stated[?]]): Decl =
    val (named, m) = Naming.helper("m", Set.empty).run(l.naming).value
    val result = Ty.yields(d.lambda.result)
    val inputs = d.lambda.params
    val (bs, lines) = (inputs.traverse(x => Naming.bind(x).map(LBinder.Explicit(_, LowerType(x.ty)))),
      LowerProg(l.env, inputs.size).block(p)).tupled.runA(named).value
    val body = if bs.isEmpty then LExpr.Do(lines, 4) else LExpr.Fun(bs, LExpr.Do(lines, 4))
    Decl.Def(List(Attr.FrflowDefs), Names.builtin(d.name.value), monad(l, d, m) ++ openBinders(l, d),
      LowerType.declaration(inputs.map(_.ty), LExpr.App(LExpr.Name(m), List(LowerType(result)))), body)

  /** The monad a program is over: any, with the errors it raises or handles and the boundaries it calls. */
  private def monad(l: Lowering, d: Define, m: LeanName): List[LBinder] =
    val ir = d.lambda.body match
      case Expr.Do(q, _) => q
      case _             => throw IllegalStateException(s"FrFlow bug: ${d.name.value} is a program with no steps")
    val v = l.resolved.theory.vocabulary
    val errors = (Progs.errors(ir) ++ Progs.boundaries(ir).flatMap(v.boundary).flatMap(_.failsWith)).distinct
    val classes = Progs.boundaries(ir).distinct.flatMap(v.boundary).map(_.className)
    LBinder.Implicit(m, LExpr.Infix(LOp.Arrow, name("Type"), name("Type"))) ::
      LBinder.Instance(LExpr.App(name("Monad"), List(LExpr.Name(m)))) ::
      errors.map(e => LBinder.Instance(LExpr.App(name("MonadExceptOf"), List(LowerType(e), LExpr.Name(m))))) ++
      classes.map(c => LBinder.Instance(LExpr.App(name(c), List(LExpr.Name(m)))))

  private def opens(l: Lowering, d: Define) = l.table.defines.get(d.name).toList.flatMap(_.symbols)

  /** The open terms a define is over: its opaque types implicit, its symbols explicit. */
  private def openBinders(l: Lowering, d: Define): List[LBinder] =
    val sorts = l.table.defines.get(d.name).toList.flatMap(_.sorts)
    sorts.map(s => LBinder.Implicit(Names.ident(s.value), name("Type"))) ++
      opens(l, d).map(s => LBinder.Explicit(Names.ident(s.value), LowerType.binder(l.table.typeOf(s))))

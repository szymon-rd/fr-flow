package frflow.proof.lean

import frflow.proof.lean.ast.*

/** Short constructors for writing Lean ASTs by hand in the tests. */
object L:
  def n(s: String): LExpr = LExpr.Name(Names.builtin(s))
  def c(s: String): LExpr = LExpr.Const(s.split('.').toList.map(Names.builtin))
  def app(f: LExpr, as: LExpr*): LExpr = LExpr.App(f, as.toList)
  def par(e: LExpr): LExpr = LExpr.Paren(e)
  def arrows(ts: LExpr*): LExpr = ts.reduceRight(LExpr.Infix(LOp.Arrow, _, _))
  def times(ts: LExpr*): LExpr = ts.reduceRight(LExpr.Infix(LOp.Times, _, _))
  def x(name: String, ty: LExpr): LBinder = LBinder.Explicit(Names.builtin(name), ty)
  def nm(s: String): LeanName = Names.builtin(s)
  def ns(s: String): List[LeanName] = s.split('.').toList.map(Names.builtin)
  def module(name: String, imports: List[String], namespace: String, decls: Decl*): LeanModule =
    val modules = imports.map(i => ModuleName(ns(i)))
    LeanModule(ModuleName(ns(name)), modules, Preamble.generated, ns(namespace), Nil, decls.toList)
  val defs: List[Attr] = List(Attr.FrflowDefs)
  /** `FrFlow.within (fun w => w.f) (fun w s => { w with f := s })`: a model's operation on its part of the world. */
  def within(field: String, op: LExpr): LExpr =
    val get = LExpr.Fun(List(LBinder.Bare(nm("w"))), LExpr.Dot(n("w"), field))
    val update = LExpr.Update(n("w"), List(nm(field) -> n("s")))
    val set = LExpr.Fun(List(LBinder.Bare(nm("w")), LBinder.Bare(nm("s"))), update)
    app(c("FrFlow.within"), par(get), par(set), par(op))

package frflow.proof.layout

import frflow.proof.prover.ast.*
import frflow.proof.prover.ast.Tree.into
import frflow.proof.prover.term.Gathered

/** The names a module's declarations use, read off its AST: the qualified constants (`Rooms.covers`,
  * `Rooms.grantWhenFree.claim`) and the plain names, from which its imports follow.
  */
object Mentioned:
  def of(ds: List[Decl]): List[List[ProverName]] = ds.flatMap(decl).distinct

  private def decl(d: Decl): List[List[ProverName]] = d match
    case Decl.Documented(_, inner)        => decl(inner)
    case Decl.Budgeted(_, inner)          => decl(inner)
    case Decl.Def(_, _, ps, t, b)         => ps.flatMap(binder) ++ expr(t) ++ expr(b)
    case Decl.Abbrev(_, _, v)             => expr(v)
    case Decl.Theorem(_, _, ps, s, p, _)  => ps.flatMap(binder) ++ expr(s) ++ proof(p)
    case Decl.Structure(_, fs)            => fs.flatMap(f => expr(f._2))
    case Decl.Inductive(_, cs)            => cs.flatMap(_._2.flatMap(binder))
    case Decl.Class(_, ps, ops)           => ps.flatMap(binder) ++ ops.flatMap(o => expr(o._2))
    case Decl.Instance(c, fs)             => expr(c) ++ fs.flatMap(f => expr(f.value))
    case Decl.Namespace(_, ds)            => ds.flatMap(decl)
    case Decl.MatchEqns                   => Nil
    case Decl.PrintAxioms(n)              => List(n)

  private def proof(p: Proof): List[List[ProverName]] = p match
    case Proof.Below(t) => expr(t)
    case _              => Nil

  private def binder(b: LBinder): List[List[ProverName]] = b.map(expr) match
    case Binding.Explicit(_, t) => t
    case Binding.Several(_, t)  => t
    case Binding.Implicit(_, t) => t
    case Binding.Instance(c)    => c
    case Binding.Bare(_)        => Nil
    case Binding.Of(_, t)       => t
    case Binding.Member(_, in)  => in

  def expr(e: LExpr): List[List[ProverName]] = e.into(Mentions)

/** The names a term uses: a plain name, a qualified constant's path, a constructor's with its type. */
private object Mentions extends Gathered[List[List[ProverName]]]:
  override def name(n: ProverName): List[List[ProverName]] = List(List(n))
  override def const(path: List[ProverName]): List[List[ProverName]] = List(path)
  override def ctor(data: ProverName, ctor: ProverName): List[List[ProverName]] = List(List(data, ctor))

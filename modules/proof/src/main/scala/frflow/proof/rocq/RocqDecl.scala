package frflow.proof.rocq

import frflow.proof.prover.ast.{Attr, Decl, LBinder, LExpr, ProverName, Proof}
import frflow.proof.rocq.RocqNames.Scope

/** Rocq's text of a declaration of the generated AST. A namespace is its declarations, each named by its whole
  * path; a structure is a record with what reads and replaces each field; a definition FrFlow's tactics unfold is
  * given to them (`Hint Unfold`) and marked as generated (`Frflow_def`), for the tactic that runs code; a theorem is a lemma proven by one of FrFlow's tactics within its budget, or
  * by the term the developer's proof file gives.
  */
private[rocq] final class RocqDecl(names: RocqNames):
  private val expr = RocqExpr(names)

  def apply(d: Decl)(using s: Scope): String = d match
    case Decl.Documented(doc, inner)      => s"(** ${doc.replace("*)", "* )")} *)\n" + apply(inner)
    case Decl.Namespace(n, ds)            =>
      ds.map(apply(_)(using s.inside(n.map(_.text)))).filter(_.nonEmpty).mkString("\n\n")
    case Decl.Def(as, n, ps, t, b)        =>
      val over = expr.over(ps)
      s"Definition ${named(n)}${params(ps)} : ${expr(t)(using over)} :=\n  ${expr(b)(using over)}." + hint(as, n)
    case Decl.Abbrev(as, n, v)            => s"Definition ${named(n)} : Type := ${expr(v)}." + hint(as, n)
    case Decl.Structure(n, fs)            => record(named(n), fs)
    case Decl.Inductive(n, cs)            => inductive(n, cs)
    case Decl.MatchEqns                   => ""
    case Decl.PrintAxioms(n)              => s"Print Assumptions ${names.constant(n.map(_.text))}."
    case Decl.Budgeted(h, t: Decl.Theorem) => theorem(t, Some(RocqDecl.seconds(h)))
    case t: Decl.Theorem                  => theorem(t, None)
    case other                            => throw RocqExpr.Unsupported(other.productPrefix)

  private def named(n: ProverName)(using s: Scope): String = names.declaring(s.namespace :+ n.text)
  private def params(ps: List[LBinder])(using Scope): String =
    ps.foldLeft(("", summon[Scope])) { case ((text, s), p) =>
      (text + " " + expr.binder(p)(using s), expr.over(List(p))(using s)) }._1

  private def hint(as: List[Attr], n: ProverName)(using Scope): String =
    if !as.contains(Attr.FrflowDefs) then ""
    else s"\n#[global] Hint Unfold ${named(n)} : frflow_defs.\n#[global] Instance : Frflow_def (@${named(n)}) := I."

  private def theorem(t: Decl.Theorem, budget: Option[Int])(using Scope): String =
    val over = expr.over(t.params)
    val tried = (tactic: String) => s"timeout ${budget.getOrElse(RocqDecl.unbudgeted)} ($tactic)"
    val proof = t.proof match
      case Proof.Rfl          => "reflexivity."
      case Proof.Below(term)  => s"exact (${expr(term)(using over)})."
      case Proof.Tactics(ls)  => ls.map(l => RocqDecl.tactics.get(l.trim).fold(
        s"fail \"FrFlow: no Rocq tactic for this proof yet\".")(known => tried(known) + ".")).mkString(" ")
    s"Lemma ${named(t.name)}${params(t.params)} : ${expr(t.statement)(using over)}.\nProof. $proof Qed."

  /** A record, its fields named by it (Rocq has one scope of field names), with, for each, what reads it off
    * any record that has a field of that name (`f_of`) and what replaces it (`with_f`).
    */
  private def record(name: String, fs: List[(ProverName, LExpr)])(using Scope): String =
    val fields = fs.map((f, t) => (RocqNames.identifier(f.text), expr(t)))
    def own(f: String) = s"${name}_$f"
    val made = fields.map((f, _) => (g: String) => if g == f then "v" else s"(${own(g)} r)")
    val instances = fields.zip(made).map { case ((f, _), replaced) =>
      s"#[global] Instance ${name}_has_$f : Has_$f $name := {| ${f}_of := ${own(f)} |}.\n" +
        s"#[global] Instance ${name}_with_$f : With_$f $name :=\n  {| with_$f := fun r v => " +
        s"${name}_mk ${fields.map(g => replaced(g._1)).mkString(" ")} |}."
    }
    (s"Record $name := ${name}_mk { ${fields.map((f, t) => s"${own(f)} : $t").mkString("; ")} }." :: instances)
      .mkString("\n")

  private def inductive(n: ProverName, cs: List[(ProverName, List[LBinder])])(using Scope): String =
    s"Inductive ${named(n)} : Type :=\n" + cs.map((c, bs) =>
      s"  | ${RocqNames.constructor(n.text, c.text)}${params(bs)}").mkString("\n") + "."

  /** The classes of the fields' names a module's structures have: one reader and one replacer for each name. */
  def fields(decls: List[Decl]): String =
    val all = decls.flatMap(RocqDecl.structures).flatMap(_.fields.map(f => RocqNames.identifier(f._1.text))).distinct
    all.map(f => s"Class Has_$f (R : Type) := { ${f}_is : Type; ${f}_of : R -> ${f}_is }.\n" +
      s"Class With_$f (R : Type) := { ${f}_takes : Type; with_$f : R -> ${f}_takes -> R }.").mkString("\n")

private[rocq] object RocqDecl:
  /** FrFlow's own tactics, by the line the lowering writes. */
  val tactics: Map[String, String] =
    List("frflow_auto", "frflow_witness", "frflow_example").map(t => t -> t).toMap

  /** The seconds a theorem with no budget of its own is given. */
  val unbudgeted: Int = 30

  /** The seconds the tactic that closes a witness is given: running the code on the values given takes long for a
    * class made of several (a payment handler's steps take over a minute), and its memory is limited apart.
    */
  val witnessed: Int = 300

  /** A try's budget in seconds on the clock: Rocq has no count of steps to stop a tactic by. */
  def seconds(heartbeats: Int): Int = (heartbeats / 1000).max(2).min(120)

  def structures(d: Decl): List[Decl.Structure] = d match
    case s: Decl.Structure       => List(s)
    case Decl.Namespace(_, ds)   => ds.flatMap(structures)
    case Decl.Documented(_, in)  => structures(in)
    case _                       => Nil

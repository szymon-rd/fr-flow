package frflow.proof.lean.print

import frflow.proof.lean.ast.*

/** A declaration's text, as today's generator lays each kind out. */
object PrintDecl:
  import Print.{dotted, expr, params}

  def apply(d: Decl): String = d match
    case Decl.Documented(doc, inner)  => s"/-- ${doc.replace("-/", "- /")} -/\n" + apply(inner)
    case Decl.Def(as, n, ps, t, b)    => s"${attrs(as)}def ${n.text}${params(ps)} : ${expr(t)} :=\n  ${expr(b)}"
    case Decl.Abbrev(as, n, v)        => s"${attrs(as)}abbrev ${n.text} : Type := ${expr(v)}"
    case Decl.Theorem(as, n, ps, s, p, b) =>
      s"${attrs(as)}theorem ${n.text}${params(ps)} :${break_(b)}${expr(s)}${proof(p)}"
    case Decl.Structure(n, fs)        => s"structure ${n.text}" + fields(fs)
    case Decl.Inductive(n, cs)        =>
      s"inductive ${n.text} where\n" + cs.map((c, bs) => s"  | ${c.text}${params(bs)}").mkString("\n")
    case Decl.Class(n, ps, ops)       => s"class ${n.text}${params(ps)} where\n" + ops.map(field).mkString("\n")
    case Decl.Instance(c, fs)         => s"instance : ${expr(c)} where\n" + fs.map(instanceField).mkString("\n")
    case Decl.Namespace(n, ds)        =>
      s"namespace ${dotted(n)}\n\n${ds.map(apply).mkString("\n\n")}\n\nend ${dotted(n)}"
    case Decl.Budgeted(h, inner)      => s"set_option maxHeartbeats $h in\n" + apply(inner)
    case Decl.MatchEqns               => "frflow_match_eqns"
    case Decl.PrintAxioms(n)          => s"#print axioms ${dotted(n)}"

  private def attrs(as: List[Attr]): String = as.map { case Attr.FrflowDefs => "@[frflow_defs] " }.mkString
  private def break_(b: Break): String = b match
    case Break.SameLine => " "
    case Break.NextLine => "\n    "
  private def proof(p: Proof): String = p match
    case Proof.Rfl         => " := rfl"
    case Proof.Below(t)    => s" :=\n  ${expr(t)}"
    case Proof.Tactics(ls) => " := by\n" + ls.map("  " + _).mkString("\n")
  private def fields(fs: List[(LeanName, LExpr)]): String =
    if fs.isEmpty then "" else " where\n" + fs.map(field).mkString("\n")
  private def field(f: (LeanName, LExpr)): String = s"  ${f._1.text} : ${expr(f._2)}"
  private def instanceField(f: InstanceField): String =
    s"  ${f.name.text}${f.params.map(" " + _.text).mkString} := ${expr(f.value)}"

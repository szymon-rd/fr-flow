package frflow.report

import frflow.Project
import frflow.dsl.LayerKind
import frflow.ledger.*
import frflow.model.*
import frflow.render.LeanPrinter

/** Status of a node combining approval and verification freshness. */
final case class NodeStatus(id: String, name: String, kind: String, approval: String, verification: String, proven: Int, total: Int):
  def coherent: Boolean = approval == "approved" && verification == "proven"

object Reports:

  def statuses(project: Project): Seq[NodeStatus] =
    val ledger = Ledger.load(project.ws)
    val hashes = project.hashes
    project.nodeIds.map { id =>
      val e = ledger.entry(id)
      val h = hashes(id)
      val approval = e.approval match
        case None                            => "unapproved"
        case Some(a) if a.specHash == h.spec => "approved"
        case Some(_)                         => "changed"
      val total = project.obligations(id).size
      val (verification, proven) = e.lastCheck match
        case None                              => ("not-checked", 0)
        case Some(c) if c.checkHash != h.check => ("stale", 0)
        case Some(c) => (c.verification.label, c.obligations.count(_.status == ObligationStatus.Proven))
      val (name, kind) =
        if id == project.TheoryId then (project.theory.name, "theory")
        else
          val l = project.theory.layerOrFail(id)
          (l.name, l.kind.label)
      NodeStatus(id, name, kind, approval, verification, proven, total)
    }

  def statusTable(project: Project): String =
    val rows = statuses(project)
    val header = Seq("NODE", "NAME", "KIND", "APPROVAL", "VERIFICATION", "OBLIGATIONS")
    val body = rows.map { s =>
      val depth = if s.id == project.TheoryId then 0 else project.theory.ancestors(project.theory.layerOrFail(s.id)).size + 1
      Seq("  " * depth + s.id, s.name, s.kind, s.approval, s.verification, s"${s.proven}/${s.total}")
    }
    val widths = header.indices.map(i => (header +: body).map(_(i).length).max)
    def fmt(r: Seq[String]) = r.zip(widths).map((c, w) => c.padTo(w, ' ')).mkString("  ").stripTrailing
    val summary =
      if rows.nonEmpty && rows.forall(_.coherent) then "Model is coherent: every node is approved and proven."
      else s"Not yet coherent: ${rows.filterNot(_.coherent).map(_.id).mkString(", ")} need approval and/or proofs."
    (fmt(header) +: body.map(fmt)).mkString("\n") + "\n\n" + summary + "\n"

  // ---------------------------------------------------------------------------
  // Structure
  // ---------------------------------------------------------------------------

  def tree(m: TheoryModel, mark: Option[String] = None): String =
    val sb = StringBuilder()
    sb ++= s"Theory ${m.name}${if mark.contains("Theory") then "   ← this node" else ""}\n"
    def go(l: LayerModel, prefix: String, last: Boolean): Unit =
      val here = if mark.contains(l.id) then "   ← this node" else ""
      val as = l.assumptionsUsed
      val note = if as.isEmpty then "" else s"   [assumes ${as.mkString(", ")}]"
      sb ++= s"$prefix${if last then "└── " else "├── "}${l.id}  ${l.name} (${l.kind.label})$note$here\n"
      val kids = m.children(l.id)
      val childPrefix = prefix + (if last then "    " else "│   ")
      kids.zipWithIndex.foreach((k, i) => go(k, childPrefix, i == kids.size - 1))
    m.roots.zipWithIndex.foreach((r, i) => go(r, "", i == m.roots.size - 1))
    sb.result()

  private def scala(code: String): String = s"```scala\n${code.trim}\n```\n"

  private def domainSection(project: Project, names: Seq[String]): String =
    val m = project.theory
    val sb = StringBuilder()
    names.foreach { n =>
      m.defs.adts.get(n).foreach { a =>
        sb ++= s"- **${a.name}**${if a.doc.nonEmpty then s": ${a.doc}" else ""}\n"
      }
      m.defs.funs.get(n).foreach { f =>
        sb ++= s"- `${f.name}`${if f.doc.nonEmpty then s": ${f.doc}" else ""}\n"
      }
    }
    sb.result()

  /** Scala sources of definitions. Methods appear inside their class; other
    * functions and values are labelled with their name.
    */
  private def sources(project: Project, names: Seq[String]): String =
    val m = project.theory
    val classSources = names.flatMap(m.defs.adts.get).map(_.source)
    names.flatMap { n =>
      m.defs.adts.get(n).map(_.source).orElse(m.defs.funs.get(n).collect {
        case f if f.source.nonEmpty && !classSources.exists(_.contains(f.source)) => s"// ${f.name}\n${f.source}"
      })
    }.filter(_.nonEmpty).distinct.mkString("\n\n")

  /** Definitions a layer uses that neither the theory nor an ancestor layer introduced. */
  def introducedBy(m: TheoryModel, l: LayerModel): List[String] =
    val before = m.theoryDefs.toSet ++ m.ancestors(l).flatMap(m.layerDefs)
    m.layerDefs(l).filterNot(before)

  private def operationsTable(l: LayerModel): String =
    val sb = StringBuilder()
    sb ++= "| Operation | Parameters | Relation to parent | Assumes | Description |\n|---|---|---|---|---|\n"
    l.ops.foreach { op =>
      val rel = op.target match
        case TargetModel.Unspecified         => ""
        case TargetModel.Refines(p, ao, _)   => s"refines `$p.$ao`"
        case TargetModel.Skip                => "new (refines skip)"
      sb ++= s"| `${op.name}` | `${LeanPrinter.tpe(op.paramType)}` | $rel | ${op.assumes.map(_.assumption).distinct.mkString(", ")} | ${op.doc} |\n"
    }
    sb.result()

  // ---------------------------------------------------------------------------
  // Slice: the bounded context an agent receives to work on one node
  // ---------------------------------------------------------------------------

  def slice(project: Project, id: String): String =
    val m = project.theory
    val r = project.renderer
    val status = statuses(project).map(s => s.id -> s).toMap
    val ledger = Ledger.load(project.ws)
    val sb = StringBuilder()
    val isTheory = id == project.TheoryId

    sb ++= s"# Slice: ${m.name} / $id\n\n"
    sb ++= "Generated by FrFlow. This slice is the complete context for work on this node. " +
      "Reload it instead of relying on earlier context.\n\n"
    sb ++= "## Position in the model\n\n```\n" + tree(m, Some(id)) + "```\n\n"

    val st = status(id)
    sb ++= s"Status: ${st.approval}, ${st.verification} (${st.proven}/${st.total} obligations).\n\n"

    val layer = if isTheory then None else Some(m.layerOrFail(id))
    val defNames = layer.fold(m.theoryDefs)(m.layerDefs)
    sb ++= "## Domain used here\n\n" + domainSection(project, defNames) + "\n"
    val src = sources(project, defNames)
    if src.nonEmpty then sb ++= scala(src) + "\n"

    if isTheory then
      if m.laws.nonEmpty then
        sb ++= "## Laws\n\n"
        m.laws.foreach(l => sb ++= s"### ${l.name}\n\n${l.statement}\n\n" + scala(l.lifted.source) + "\n")
      if m.assumptions.nonEmpty then
        sb ++= "## Assumptions\n\n"
        m.assumptions.foreach(a => sb ++= s"- **${a.id} ${a.name}.** ${a.statement} Justification: ${a.justification}\n")
        sb ++= "\n"
    layer.foreach { l =>
      sb ++= "## Path from the root\n\n"
      m.pathFromRoot(l).foreach { a =>
        val here = if a.id == l.id then " (this layer)" else ""
        sb ++= s"### ${a.id} ${a.name}, ${a.kind.label}$here\n\n"
        sb ++= s"**Statement.** ${a.statement}\n\n**Rationale.** ${a.rationale}\n\n"
        a.invariants.foreach { i =>
          val what = if i.requirement then "Requirement" else "Invariant"
          sb ++= s"**$what `${i.name}`.** ${i.doc}\n\n" + scala(i.lifted.source) + "\n"
        }
      }

      sb ++= s"## Operations of ${l.id}\n\n" + operationsTable(l) + "\n"
      l.ops.foreach { op =>
        sb ++= s"### `${op.name}`\n\n"
        op.assumes.foreach(a => sb ++= s"assume (${a.assumption}):\n" + scala(a.lifted.source))
        op.checks.foreach(c => sb ++= "check:\n" + scala(c.source))
        op.act.foreach(a => sb ++= "act:\n" + scala(a.source))
        op.target match
          case TargetModel.Refines(p, ao, w) => sb ++= s"refines `$p.$ao` with witness:\n" + scala(w.source)
          case _                             => ()
        sb ++= "\n"
      }
      l.link.foreach { link =>
        sb ++= "## Link to the parent\n\nabstraction:\n" + scala(link.abs.source)
        link.glue.foreach(g => sb ++= "glue:\n" + scala(g.source))
        sb ++= "\n"
      }

      val gs = r.guarantees(l)
      if gs.nonEmpty then
        sb ++= s"## Properties guaranteed at ${l.id}\n\n"
        sb ++= "Each holds in every reachable state once this layer and its ancestors are proven.\n\n"
        gs.foreach { g =>
          val src = if g.isOwn then "declared here" else s"inherited from ${g.origin}"
          sb ++= s"- `${g.invariant}` ($src): theorem `${m.name}.${g.theoremName}`\n"
        }
        sb ++= "\n"

      val inScope = m.pathFromRoot(l).flatMap(_.assumptionsUsed).distinct
      if inScope.nonEmpty then
        sb ++= "## Assumptions in scope\n\n"
        inScope.flatMap(m.assumption).foreach(a => sb ++= s"- **${a.id} ${a.name}.** ${a.statement} Justification: ${a.justification}\n")
        sb ++= "\n"

      m.parentOf(l).foreach(p => sb ++= s"## Generated Lean model of the parent (${p.id})\n\n```lean\n${r.renderModel(p)}```\n\n")
      sb ++= s"## Generated Lean model of ${l.id}\n\n```lean\n${r.renderModel(l)}```\n\n"
    }

    val results = ledger.entry(id).lastCheck.filter(c => project.hashes.get(id).exists(_.check == c.checkHash))
      .map(_.obligations.map(o => o.name -> o).toMap).getOrElse(Map.empty)
    sb ++= s"## Obligations of $id\n\n"
    sb ++= "Each is first attempted by `frflow_auto`. Open ones need a proof in " +
      s"`lean/${r.proofsPath(id)}` as `theorem <name> : Obl.<name>` (`scaffold $id` creates stubs).\n\n"
    project.obligations(id).foreach { o =>
      val st = results.get(o.name).map(x => x.status.label + (if x.detail.nonEmpty then s" (${x.detail})" else "")).getOrElse("not checked")
      sb ++= s"### `${o.name}`: $st\n\n${o.description}\n\n```lean\ndef ${o.name} : Prop :=\n  ${o.statement}\n```\n\n"
    }

    sb ++= """## Rules for work on this node
             |
             |- The model is the Scala code. Change behaviour, types or properties only there, then render again.
             |- Never edit generated files (`FrFlowGen/`, `FrFlowAudit/`): they are overwritten.
             |- Write proofs only in the node's proof file, and only for obligations automation does not prove.
             |  Helper lemmas are allowed. A proof must state exactly `Obl.<name>`.
             |- `axiom`, `admit`, `native_decide`, `implemented_by`, `extern`, `unsafe` and `opaque` are rejected.
             |- If an obligation is false, do not work around it: report it and propose a change to the model
             |  (statement, operation, abstraction, invariant or assumption), with rationale. Model changes need
             |  human approval.
             |""".stripMargin
    sb.result()

  // ---------------------------------------------------------------------------
  // Digest: the human-readable theory
  // ---------------------------------------------------------------------------

  def digest(project: Project): String =
    val m = project.theory
    val r = project.renderer
    val status = statuses(project).map(s => s.id -> s).toMap
    val sb = StringBuilder()
    sb ++= s"# Theory: ${m.name}\n\n"
    sb ++= "Generated by FrFlow from the Scala model. Do not edit; change the model and run `digest` again.\n\n"
    sb ++= "## Structure\n\n```\n" + tree(m) + "```\n\n"
    sb ++= "## Status\n\n```\n" + statusTable(project) + "```\n\n"

    sb ++= "## Domain\n\n"
    sb ++= "Scala ADTs and functions shared by every layer and used directly by the implementation.\n\n"
    sb ++= domainSection(project, m.theoryDefs) + "\n"
    val src = sources(project, m.theoryDefs)
    if src.nonEmpty then sb ++= scala(src) + "\n"

    if m.laws.nonEmpty then
      sb ++= "## Laws\n\n"
      m.laws.foreach(l => sb ++= s"- **${l.name}.** ${l.statement}\n")
      sb ++= "\n"

    if m.assumptions.nonEmpty then
      sb ++= "## Assumptions\n\n"
      sb ++= "Guarantees hold for every environment that satisfies these assumptions.\n\n"
      m.assumptions.foreach(a => sb ++= s"- **${a.id} ${a.name}.** ${a.statement}\n  *Justification:* ${a.justification}\n")
      sb ++= "\n"

    sb ++= "## Layers\n\n"
    m.topological.foreach { l =>
      val st = status(l.id)
      sb ++= s"### ${l.id} ${l.name} (${l.kind.label})\n\n"
      l.parent.foreach(p => sb ++= s"Refines **$p**. ")
      sb ++= s"Status: ${st.approval}, ${st.verification}.\n\n"
      sb ++= s"${l.statement}\n\n*Rationale:* ${l.rationale}\n\n"
      val own = introducedBy(m, l)
      if own.nonEmpty then
        sb ++= "Types and functions introduced here:\n\n" + domainSection(project, own) + "\n"
        sb ++= scala(sources(project, own)) + "\n"
      if l.ops.nonEmpty then sb ++= operationsTable(l) + "\n"
      l.invariants.foreach { i =>
        sb ++= s"- ${if i.requirement then "Requirement" else "Invariant"} **${i.name}**: ${i.doc}\n"
      }
      if l.invariants.nonEmpty then sb ++= "\n"
      val gs = r.guarantees(l)
      if gs.nonEmpty then
        sb ++= "Guarantees: " + gs.map(g => if g.isOwn then s"`${g.invariant}`" else s"`${g.invariant}` (from ${g.origin})").mkString(", ") + ".\n\n"
      if l.kind == LayerKind.Implementation then
        sb ++= "This layer is executable: `frflow.runtime.Service` runs its operations as Scala code.\n\n"
    }
    sb.result()

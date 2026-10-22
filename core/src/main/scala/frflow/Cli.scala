package frflow

import java.nio.file.Paths

/** Command line of a kb:
  * {{{
  * @main def auth(args: String*): Unit = sys.exit(knowledge.cli(args, root = "examples/auth"))
  * }}}
  */
object Cli:
  val usage: String =
    """Usage: <kb> <command>
      |
      |  render                  generate Lean and the snapshot .frflow/kb.json from the Scala definitions
      |  check [NODE]            render, prove each node from its parts, record the results
      |  status                  the tree: decisions, proofs, examples, what is trusted; exits 1 unless the knowledge base is complete
      |  ci                      for CI: check, then status; exits 1 unless everything is proven and decided
      |  inbox                   start here: the developer's open requests, what is yours to do, what waits for the developer
      |  context NODE            everything needed to work on NODE (for agents and people)
      |  find WORDS|PATH         the nodes that govern a file, or what mentions some words (nodes, reasons, rejected options, the idea)
      |  scaffold NODE           a proof file for an obligation automation did not prove
      |
      |Decisions are the developer's, and are made in the browser (bin/frflow serve).
      |""".stripMargin

  def run(kb: KnowledgeBase, ws: Workspace, args: Seq[String]): Int =
    val problems = kb.problems
    if problems.nonEmpty then
      problems.foreach(p => System.err.println(s"error: $p"))
      return 1
    val w = Workflow(kb, ws)
    def node(id: String)(f: Node[?] => Int): Int =
      kb.node(id).fold { System.err.println(s"unknown node $id"); 1 }(f)
    args.toList match
      case "check" :: rest =>
        if !Lake(ws.lean).available then { System.err.println("lake not found (set FRFLOW_LAKE)"); return 3 }
        if rest.headOption.exists(kb.node(_).isEmpty) then { System.err.println(s"unknown node ${rest.head}"); return 1 }
        val results = w.check(rest.headOption)
        w.writeSnapshot()
        var examplesFail = false
        results.foreach { (n, c) =>
          // The node's status, with what else is open, and failing examples first: they show the code
          // (or the contract) is wrong, which no proof fixes.
          val open = c.obligations.filter(r => !r.isEvaluation && !r.fine)
          println(s"${n.id}: ${c.status}${if c.status == "proven" && open.nonEmpty then s" (not proven: ${open.map(_.name).mkString(", ")})" else ""}")
          val failing = kb.exampleResults(n).filter(r => r.contract != "ok" || r.implementation.exists(_ != "ok"))
          if failing.nonEmpty then
            examplesFail = true
            println(s"  ${failing.size} example(s) fail: the code or the contract is wrong; fix that, not the proof")
            failing.take(5).foreach(r => println(s"    ${r.example.describe}: ${r.verdict}"))
          // `idle` is not an obligation: proven, it says the root is met by doing nothing.
          c.obligations.filter(r => !r.isLimit && r.status != "proven").foreach(r => println(s"  ${r.status} ${r.name}: ${r.detail.linesIterator.mkString("\n    ")}"))
          c.obligations.filter(r => r.name == "idle" && r.status == "proven").foreach(r => println(
            s"  ! doing nothing meets it (${r.detail}): state what users can do, so it says exactly what the system does (status fails until then)"))
          // With an example failing, the link may be false: no hint to prove it.
          c.messages.filterNot(m => failing.nonEmpty && m.startsWith("prove it in")).foreach(m => println(s"  ! ${m.linesIterator.mkString("\n    ")}"))
        }
        println()
        print(w.status._1)
        if results.forall(_._2.status == "proven") && !examplesFail then 0 else 1
      case "ci" :: Nil =>
        // What CI runs: check (a node whose formal parts did not change keeps its result), then status.
        if !Lake(ws.lean).available then { System.err.println("lake not found (set FRFLOW_LAKE)"); return 3 }
        // Results kept from a cache are trusted as far as the cache is: some are proven again, at random
        // (FRFLOW_VERIFY, the fraction, 0.05 by default), and one that does not hold any more fails CI.
        val fraction = sys.env.get("FRFLOW_VERIFY").flatMap(_.toDoubleOption).getOrElse(0.05)
        val again = w.sample(fraction)
        val results = w.check(verify = again)
        val untrue = results.filter((n, c) => again(n.id) && c.status != "proven")
        untrue.foreach((n, c) => println(s"${n.id}: recorded as proven, but proven again it is ${c.status}: the recorded results are not to be trusted; check without them"))
        if again.nonEmpty then println(s"Proven again from scratch, to verify the recorded results: ${again.toList.sorted.mkString(", ")}")
        results.filter(_._2.status != "proven").foreach((n, c) => println(s"${n.id}: ${c.status}"))
        // The ledger only grows: nothing decided where this branch left its base (FRFLOW_BASE, by
        // default origin's default branch) may be missing now.
        val base = sys.env.get("FRFLOW_BASE").orElse(Some("origin/HEAD")).flatMap(Git.mergeBase(ws.root, _))
        val lost = base.flatMap(b => Git.show(ws.root, b, ws.root.relativize(ws.ledgerFile).toString)).toList
          .flatMap(t => Ledger.lost(Ledger.fromJson(Json.parse(t)), Ledger.load(ws.ledgerFile)))
        lost.foreach((id, d) => println(s"$id: the ${d.action} of ${d.at} by ${d.by}, in the ledger at ${base.get.take(12)}, is gone from it: restore it (merge the ledger with `frflow merge-ledger`)"))
        val (text, ok) = w.status
        print(text)
        if ok && lost.isEmpty && results.forall(_._2.status == "proven") then 0 else 1
      case "render" :: Nil =>
        val changed = w.render()
        println(s"rendered ${changed.size} changed file(s); wrote ${ws.root.relativize(w.writeSnapshot())}")
        0
      // The snapshot is written too, so the browser shows what status says.
      case "status" :: Nil => w.writeSnapshot(); val (text, ok) = w.status; print(text); if ok then 0 else 1
      case "inbox" :: Nil => println(Decisions.inbox(Some(w.annotated), w.requests)); 0
      case "context" :: id :: Nil => node(id) { n => print(w.context(n)); 0 }
      case "find" :: query if query.nonEmpty => println(Decisions.find(w.annotated, query.mkString(" "))); 0
      case "scaffold" :: id :: Nil =>
        node(id) { n =>
          println(if w.scaffold(n) then s"created lean/${w.generate.proofsPath(n.id)}" else "nothing to create")
          w.writeSnapshot()
          0
        }
      case _ => System.err.println(usage); 2

  /** The workspace at `FRFLOW_ROOT`, or `default`; `kernelPath` is relative to its `lean/`. */
  def workspace(default: String, kernelPath: String): Workspace =
    Workspace(Paths.get(sys.env.getOrElse("FRFLOW_ROOT", default)).toAbsolutePath.normalize, kernelPath)

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
      |  check [NODE]            render, prove the links, record the results
      |  status                  the tree: decisions, links, examples; exits 1 unless the knowledge base is complete (for CI)
      |  context NODE            everything needed to work on NODE (for agents and people)
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
        results.foreach { (n, c) =>
          println(s"${n.id}: ${c.status}")
          // `idle` is not an obligation: proven, it is a limit of the contract (it allows doing nothing).
          c.obligations.filter(r => r.name != "idle" && r.status != "proven").foreach(r => println(s"  ${r.status} ${r.name}: ${r.detail}"))
          c.obligations.filter(r => r.name == "idle" && r.status == "proven").foreach(r => println(s"  limit: it is met by ${r.detail} on every call"))
          c.messages.foreach(m => println(s"  ! ${m.linesIterator.mkString("\n    ")}"))
        }
        println()
        print(w.status._1)
        if results.forall(_._2.status == "proven") then 0 else 1
      case "render" :: Nil =>
        val changed = w.render()
        println(s"rendered ${changed.size} changed file(s); wrote ${ws.root.relativize(w.writeSnapshot())}")
        0
      case "status" :: Nil => val (text, ok) = w.status; print(text); if ok then 0 else 1
      case "context" :: id :: Nil => node(id) { n => print(w.context(n)); 0 }
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

package frflow

import java.nio.file.Paths

/** Command line of a project:
  * {{{
  * @main def wallet(args: String*): Unit = sys.exit(Cli.run(WalletProject, Cli.workspace("examples/wallet"), args))
  * }}}
  */
object Cli:
  val usage: String =
    """Usage: <project> <command>
      |
      |  check [NODE]            generate Lean, run scenarios, prove obligations, record results
      |  status                  the knowledge base with approval and verification state
      |  context NODE            everything needed to work on NODE (for agents and people)
      |  approve NODE --by NAME  record the developer's approval of NODE
      |  scaffold NODE [--all]   proof stubs for obligations automation did not prove
      |""".stripMargin

  def run(project: Project, ws: Workspace, args: Seq[String]): Int =
    val problems = project.problems
    if problems.nonEmpty then
      problems.foreach(p => System.err.println(s"error: $p"))
      return 1
    val w = Workflow(project, ws)
    def node(id: String)(f: Node[?, ?] => Int): Int =
      project.node(id).fold { System.err.println(s"unknown node $id"); 1 }(f)
    args.toList match
      case "check" :: rest =>
        if !Lake(ws.lean).available then { System.err.println("lake not found (set FRFLOW_LAKE)"); return 3 }
        if rest.headOption.exists(project.node(_).isEmpty) then { System.err.println(s"unknown node ${rest.head}"); return 1 }
        val results = w.check(rest.headOption)
        results.foreach { (n, c) =>
          println(s"${n.id}: ${c.status}")
          (c.scenarios ++ c.obligations).filterNot(r => r.status == "ok" || r.status == "proven")
            .foreach(r => println(s"  ${r.status} ${r.name}: ${r.detail}"))
          c.messages.foreach(m => println(s"  ! ${m.linesIterator.mkString("\n    ")}"))
        }
        println()
        print(w.status)
        if results.forall(_._2.status == "proven") then 0 else 1
      case "status" :: Nil => print(w.status); 0
      case "context" :: id :: Nil => node(id) { n => print(w.context(n)); 0 }
      case "approve" :: id :: "--by" :: who :: Nil => node(id) { n => w.approve(n, who); println(s"approved ${n.id} by $who"); 0 }
      case "scaffold" :: id :: rest =>
        node(id) { n =>
          val added = w.scaffold(n, rest.contains("--all"))
          println(if added.isEmpty then "nothing to add" else s"added ${added.mkString(", ")} to lean/${w.generate.proofsPath(n.id)}")
          0
        }
      case _ => System.err.println(usage); 2

  /** The workspace at `FRFLOW_ROOT`, or `default`; the kernel is found relative to it. */
  def workspace(default: String, kernelPath: String = "../../../lean"): Workspace =
    Workspace(Paths.get(sys.env.getOrElse("FRFLOW_ROOT", default)).toAbsolutePath.normalize, kernelPath)

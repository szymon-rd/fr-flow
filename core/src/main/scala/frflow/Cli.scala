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
      |  status                  the knowledge base with approval and verification state
      |  context NODE            everything needed to work on NODE (for agents and people)
      |  approve NODE --by NAME  record the developer's approval of NODE
      |  scaffold NODE           a proof file for an obligation automation did not prove
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
          c.obligations.filterNot(_.status == "proven")
            .foreach(r => println(s"  ${r.status} ${r.name}: ${r.detail}"))
          c.messages.foreach(m => println(s"  ! ${m.linesIterator.mkString("\n    ")}"))
        }
        println()
        print(w.status)
        if results.forall(_._2.status == "proven") then 0 else 1
      case "render" :: Nil =>
        val changed = w.render()
        w.record("render", kb.root.id, "changed" -> Json.JNum(changed.size.toDouble))
        println(s"rendered ${changed.size} changed file(s); wrote ${ws.root.relativize(w.writeSnapshot())}")
        0
      case "status" :: Nil => print(w.status); 0
      case "context" :: id :: Nil => node(id) { n => print(w.context(n)); 0 }
      case "approve" :: id :: "--by" :: who :: Nil =>
        node(id) { n => w.approve(n, who); w.writeSnapshot(); println(s"approved ${n.id} by $who"); 0 }
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

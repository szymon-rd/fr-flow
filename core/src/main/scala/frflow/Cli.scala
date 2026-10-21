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
      |  status                  the tree: decisions, links, examples; exits 1 unless all is settled (for CI)
      |  context NODE            everything needed to work on NODE (for agents and people)
      |  accept NODE --by NAME --reason TEXT [--reject ID,ID] [--revisit ID,ID] [--subtree]
      |                          the developer's decision: choose NODE (rejecting alternatives), or
      |                          accept it again after something moved under it, or agree it is gone;
      |                          --revisit puts decisions below that the change may affect up for review;
      |                          --subtree also accepts the nodes below that moved only because it did
      |  reject NODE --by NAME --reason TEXT
      |                          the developer's decision: reject a proposal, choosing nothing instead
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
        print(w.status._1)
        if results.forall(_._2.status == "proven") then 0 else 1
      case "render" :: Nil =>
        val changed = w.render()
        println(s"rendered ${changed.size} changed file(s); wrote ${ws.root.relativize(w.writeSnapshot())}")
        0
      case "status" :: Nil => val (text, ok) = w.status; print(text); if ok then 0 else 1
      case "context" :: id :: Nil => node(id) { n => print(w.context(n)); 0 }
      case "accept" :: id :: rest =>
        val flags = Set("--subtree")
        val opts = rest.filterNot(flags).grouped(2).collect { case List(k, v) if k.startsWith("--") => k.drop(2) -> v }.toMap
        if rest.filterNot(flags).size % 2 != 0 || !opts.contains("by") || opts.keySet.exists(!Set("by", "reason", "reject", "revisit")(_)) then
          System.err.println(usage); return 2
        def ids(k: String) = opts.get(k).toList.flatMap(_.split(",")).map(_.trim).filter(_.nonEmpty)
        val req = Decisions.Request(id, opts("by"), opts.getOrElse("reason", ""), ids("reject"), rest.contains("--subtree"), ids("revisit"))
        w.decide(req) match
          case Left(why) => System.err.println(why); 1
          case Right(()) =>
            w.writeSnapshot()
            println(s"accepted $id by ${req.by}${if req.reject.nonEmpty then s"; rejected ${req.reject.mkString(", ")}" else ""}")
            0
      case "reject" :: id :: "--by" :: by :: "--reason" :: reason :: Nil =>
        w.decide(Decisions.Request(id, by, reason, List(id))) match
          case Left(why) => System.err.println(why); 1
          case Right(()) => w.writeSnapshot(); println(s"rejected $id by $by"); 0
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

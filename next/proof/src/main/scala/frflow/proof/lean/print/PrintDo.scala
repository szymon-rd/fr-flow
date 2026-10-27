package frflow.proof.lean.print

import frflow.proof.lean.ast.*

/** The lines of a `do` block, each kind laid out as today's printer does (`LeanPrinter.block`). */
object PrintDo:
  import Print.expr

  def line(l: DoLine, ind: String): List[String] = l match
    case DoLine.Bind(n, s)          => List(s"${ind}let ${n.text} ← ${expr(s)}")
    case DoLine.Let(n, v)           => List(s"${ind}let ${n.text} := ${expr(v)}")
    case DoLine.Step(s)             => List(ind + expr(s))
    case DoLine.BindBlock(n, body)  => s"$ind${n.fold("do")(x => s"let ${x.text} ← do")}" :: block(body, ind + "  ")
    case DoLine.For(x, over, body)  => s"${ind}for ${x.text} in ${expr(over)} do" :: block(body, ind + "  ")
    case DoLine.Branch(c, a, b)     =>
      (s"${ind}if ${expr(c)} then" :: block(a, ind + "  ")) ++ (s"${ind}else" :: block(b, ind + "  "))
    case DoLine.TryCatch(lead, e, body, x, handler) =>
      val head = s"$ind${lead.fold("")(n => s"let ${n.text} ← ")}tryCatchThe ${expr(e)} (do"
      (head :: closed(block(body, ind + "    "))) ++
        closed(s"$ind  (fun ${x.fold("_")(_.text)} => do" :: block(handler, ind + "    "))
    case DoLine.Traverse(lead, head, ps, body) =>
      s"$ind${lead.fold("")(n => s"let ${n.text} ← ")}${expr(head)} fun ${ps.map(_.text).mkString(" ")} => do" ::
        block(body, ind + "  ")

  private def block(ls: List[DoLine], ind: String): List[String] = ls.flatMap(line(_, ind))
  /** The lines, the last closing the parenthesis the block opened (a block has a line at least). */
  private def closed(ls: List[String]): List[String] = ls.reverse match
    case last :: before => (s"$last)" :: before).reverse
    case Nil            => List(")")

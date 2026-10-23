package frflow
package lean

import cats.syntax.all.*
import frflow.protocol.ObligationName

/** An example, evaluated in Lean: `claim` is what Scala computes of it (the contract's verdict, or the
  * result of the proven implementation), `opposite` its negation. Lean proving the opposite means the
  * translation does not mean what the Scala does.
  */
final case class Eval(name: ObligationName, what: String, claim: String, opposite: String)

/** The examples of the contracts of a knowledge base, and probes near them, evaluated in Lean. */
final class Evals(kb: KnowledgeBase, refinement: Refinement, values: LeanValues):
  import refinement.*
  import refinement.vocabulary.*
  import values.*

  /** Lean parameter names, with the Param objects they stand for. */
  private val paramObject: Map[String, Param[?]] =
    (kb.nodes.flatMap(_.referenced) ++ kb.defs.map(_.lifted)).flatMap(l => l.paramRefs.map(_._1).zip(l.paramObjects)).toMap ++
      kb.nodes.flatMap(_.op).map(o => o.name -> o)

  /** The examples of a contract Lean evaluates, and why the others are not evaluated (by `eval_i`); then
    * probes (`probe_j`): inputs near the examples' (see `Probes.near`), each run in Scala and evaluated in
    * Lean, so that the translation is cross-checked where the examples do not reach. A probe Lean cannot
    * evaluate is left out; one it evaluates otherwise than Scala fails the node, as an example does.
    */
  def evals(n: Node[?]): (List[Eval], List[(ObligationName, String)]) =
    (n.post, n.op) match
      case (Some(post), Some(op)) if formal(n) => Contract(n, post, op.name).all
      case _                                   => (Nil, Nil)

  private final class Contract(n: Node[?], post: Lifted[?], op: String):
    // The post's Scala value takes the call's inputs and result: its type is erased in the node.
    private val holds = post.value.asInstanceOf[(Any, Any, Any) => Boolean]
    private val impl = provenImpl(n)

    def all: (List[Eval], List[(ObligationName, String)]) =
      val (failed, evaluated) = n.cases.zipWithIndex.partitionMap { (e, i) =>
        val label = s"example ${i + 1} (${e.note})"
        one(ObligationName.Eval(i), label, e.bindings, e.a, e.b, Some(e.result)).left.map(why => (ObligationName.Eval(i), s"$label: $why"))
      }
      (evaluated.flatten ++ probes, failed)

    /** Lean for the value an example gives an open term: a binding's value, a finite table as a
      * function looking it up, or a call of another operation as its proven code (which the example runs).
      */
    private def valueOf(bindings: List[Binding], p: String, seen: Set[String]): Either[String, String] =
      paramObject.get(p).flatMap(po => bindings.find(_.param eq po)) match
        case Some(b) => b.table.fold(scalaValue(p, b))(tableValue(p, _))
        case None => kb.onOp.getOrElse(p, Nil).flatMap(provenImpl).headOption.filterNot(_ => seen(p)) match
          case Some(d) => envOf(bindings, defCtx(d), seen + p).map(env => code(d, env)._1)
          case None    => Left(s"it gives no value for $p")

    private def scalaValue(p: String, b: Binding): Either[String, String] =
      scala.util.Try(b.value()).toOption.flatMap(leanValue)
        .toRight(s"Lean has no value for $p (a function, or a type Lean does not have; give a lookup as bindTable)")

    private def tableValue(p: String, table: Map[?, ?]): Either[String, String] =
      val domain = paramType(p).map(LeanType.parse) match
        case Some(LeanType.Fun(t)) => t.stripPrefix("(").stripSuffix(")").split("→").headOption.map(_.trim)
        case _                     => None
      val cases = table.toList.traverse((k, v) => (leanValue(k), leanValue(v)).tupled)
      (domain, cases).tupled.map((dom, kvs) => s"(fun (k' : $dom) => ${lookup(kvs)})").toRight(s"Lean has no value for the table $p")

    private def envOf(bindings: List[Binding], c: Ctx, seen: Set[String]): Either[String, Env] =
      val opens = Ctx.all(c.names.map(term(_)._2))
      if opens.opaques.nonEmpty then Left(s"the contract leaves ${opens.opaques.mkString(", ")} open")
      else opens.params.traverse(p => valueOf(bindings, p, seen).map(v => p -> (v, Ctx.empty))).map(_.toMap)

    /** What Scala computes of a call: the post's verdict on the result (the example's, else the code's),
      * the code's result, and the result judged.
      */
    private def run(bindings: List[Binding], a: Any, b: Any, result: Option[Any]): Either[String, (Option[Boolean], Option[Any], Option[Any])] =
      scala.util.Try(Bindings.within(kb.opCode ++ kb.definitionBindings ++ bindings) {
        // A proven implementation's Scala value takes the call's inputs: its type is erased in the node.
        val got = impl.map(d => d.fn.asInstanceOf[(Any, Any) => Any](a, b))
        val r = result.orElse(got)
        (r.map(holds(a, b, _)), got, r)
      }).toEither.left.map(x => s"Scala cannot evaluate it: ${x.getMessage}")

    /** One call evaluated: of the contract, and of the proven code (with a name of its own). */
    private def one(name: ObligationName, label: String, bindings: List[Binding], a: Any, b: Any, result: Option[Any]): Either[String, List[Eval]] =
      for
        env <- envOf(bindings, ctx(post) ++ impl.fold(Ctx.empty)(defCtx), Set(op))
        ran <- run(bindings, a, b, result)
        (verdict, got, judged) = ran
        ta <- leanValue(a).toRight("Lean has no value for its input")
        tb <- leanValue(b).toRight("Lean has no value for its input")
        tr <- judged.traverse(r => leanValue(r).toRight("Lean has no value for its result"))
      yield
        val onPost = (verdict, tr).tupled.map { (v, t) =>
          val call = s"${app(qualified(n, "post"), ctx(post), env)._1} $ta $tb $t"
          Eval(name, label, if v then call else s"¬ $call", if v then s"¬ $call" else call)
        }
        val onImpl = for { d <- impl; g <- got; tg <- leanValue(g) } yield
          val f = code(d, env)._1
          Eval(name.ofCode, s"$label, run by ${d.name}", s"$f $ta $tb = $tg", s"$f $ta $tb ≠ $tg")
        onPost.toList ++ onImpl.toList

    /** Probes: with the first example's bindings, inputs near the examples' that no example has; half at a
      * boundary (a number of one input equal to one of the other, where `<` and `<=` part), half anywhere.
      */
    private def probes: List[Eval] = n.cases.headOption.toList.flatMap { first =>
      val inputs = Probes.inputs(n.cases)
      // Without code to run, the post is judged on the examples' results.
      val calls = if impl.isDefined then inputs.map((a, b) => (a, b, None))
        else inputs.flatMap((a, b) => n.cases.map(_.result).distinct.map(r => (a, b, Some(r))))
      val (edge, rest) = scala.util.Random(n.id.hashCode).shuffle(calls)
        .partition((a, b, _) => Probes.numbers(a).toSet.intersect(Probes.numbers(b).toSet).nonEmpty)
      interleave(edge, rest).iterator.zipWithIndex
        .flatMap { case ((a, b, r), j) => one(ObligationName.Probe(j), s"probe ${j + 1}", first.bindings, a, b, r).toOption }
        .filter(_.nonEmpty).take(Generate.ProbeCount).flatten.toList
    }

  /** `x0 y0 x1 y1 …`, the longer list's rest at the end. */
  private def interleave[A](xs: List[A], ys: List[A]): List[A] =
    xs.map(Some(_)).zipAll(ys.map(Some(_)), None, None).flatMap((x, y) => x.toList ++ y.toList)

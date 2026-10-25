package frflow
package lean
package obligation

import cats.syntax.all.*
import frflow.protocol.ObligationName

/** The examples of the contracts of a knowledge base, and probes near them, evaluated in Lean. */
final class Evals(kb: KnowledgeBase, refinement: Refinement):
  import refinement.*
  import refinement.vocabulary.*
  private val K = kb.name
  private val typeNames: Set[String] = kb.types.map(_.name).toSet

  private val paramObject: Map[String, Param[?]] =
    (kb.nodes.flatMap(_.referenced) ++ kb.defs.map(_.lifted)).flatMap(l => l.paramRefs.map(_._1).zip(l.paramObjects)).toMap ++
      kb.nodes.flatMap(_.op).map(o => o.name -> o)

  /** The examples Lean evaluates, why the others are not, and probes near them where the examples do not reach. */
  def evals(n: Node[?]): (List[Eval], List[(ObligationName, String)]) =
    (n.post, n.op) match
      case (Some(post), Some(op)) if formal(n) => Contract(n, post, op.name).all
      case _                                   => (Nil, Nil)

  private final class Contract(n: Node[?], post: Lifted[?], op: String):
    // The post's Scala value takes the call's inputs and result: its type is erased in the node.
    // A flow's post takes the inputs, the result, the world before and the world after: `postFn` gives it a call's.
    private val holds: (List[Any], Any) => Boolean =
      n.postFn.getOrElse((ins, r) => Fn.call(post.value, ins :+ r).asInstanceOf[Boolean])
    private val impl = provenImpl(n)
    // The other nodes' proven code the examples' world is computed with: the eval module imports it.
    private val used = scala.collection.mutable.LinkedHashSet.empty[Def[?]]

    def all: (List[Eval], List[(ObligationName, String)]) =
      val (failed, evaluated) = n.cases.zipWithIndex.partitionMap { (e, i) =>
        val label = s"example ${i + 1} (${e.note})"
        one(ObligationName.Eval(i), label, e.bindings, e.inputs, Some(e.result)).left.map(why => (ObligationName.Eval(i), s"$label: $why"))
      }
      val es = evaluated.flatten ++ probes
      (es.map(_.copy(defs = used.toList)), failed)

    private def valueOf(bindings: List[Binding], p: String, seen: Set[String]): Either[String, String] =
      paramObject.get(p).flatMap(po => bindings.find(_.param eq po)) match
        case Some(b) => b.table.fold(scala.util.Try(b.value()).toOption.flatMap(leanValue)
          .toRight(s"Lean has no value for $p (a function, or a type Lean does not have; give a lookup as bindTable)"))(tableValue(p, _))
        case None => kb.onOp.getOrElse(p, Nil).flatMap(provenImpl).headOption.filterNot(_ => seen(p)) match
          case Some(d) => envOf(bindings, defCtx(d), seen + p).map(env => { used += d; code(d, env)._1 })
          case None    => Left(s"it gives no value for $p")

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

    private def run(bindings: List[Binding], ins: List[Any], result: Option[Any]): Either[String, (Option[Boolean], Option[Any], Option[Any])] =
      scala.util.Try(Bindings.within(kb.opCode ++ kb.definitionBindings ++ bindings) {
        // A proven implementation's Scala value takes the call's inputs: its type is erased in the node.
        val got = impl.map(d => Fn.call(d.fn, ins))
        val r = result.orElse(got)
        (r.map(holds(ins, _)), got, r)
      }).toEither.left.map(x => s"Scala cannot evaluate it: ${x.getMessage}")

    private def one(name: ObligationName, label: String, bindings: List[Binding], ins: List[Any], result: Option[Any]): Either[String, List[Eval]] =
      for
        env <- envOf(bindings, ctx(post) ++ impl.fold(Ctx.empty)(defCtx), Set(op))
        ran <- run(bindings, ins, result)
        (verdict, got, judged) = ran
        tins <- ins.traverse(x => leanValue(x).toRight("Lean has no value for its input"))
        tr <- judged.traverse(r => leanValue(r).toRight("Lean has no value for its result"))
      yield
        val args = tins.map(" " + _).mkString
        val onPost = (verdict, judged, tr).tupled.map { (v, r, t) =>
          val p = app(qualified(n, "post"), ctx(post), env)._1
          val call = r match
            // A run's result and world after, as the post takes them: inputs, result, world before, world after.
            // A run that may fail: the post of a result, the failure clause of an error (`FrFlow.outcome`).
            case (x, w) if n.isFlow && n.failure.isDefined =>
              val (as, before) = (tins.init.map(" " + _).mkString, tins.last)
              val fail = n.failure.flatMap(_.post).fold(qualified(n, "failure"))(fp => app(qualified(n, "failure"), ctx(fp), env)._1)
              (leanValue(outcome(x)), leanValue(w)).tupled.fold(s"$p$as $t $before")((tx, tw) =>
                s"FrFlow.outcome (fun r' w' => $p$as r' $before w') (fun e' w' => $fail e' $before w') ($tx, $tw)")
            case (x, w) if n.isFlow =>
              val (as, before) = (tins.init.map(" " + _).mkString, tins.last)
              (leanValue(x), leanValue(w)).tupled.fold(s"$p$as $t $before")((tx, tw) => s"$p$as $tx $before $tw")
            case _ => s"$p$args $t"
          Eval(name, label, if v then call else s"¬ $call", if v then s"¬ $call" else call)
        }
        val onImpl = for { d <- impl; g <- got; tg <- leanValue(if n.failure.isDefined then g match { case (x, w) => (outcome(x), w); case o => o } else g) } yield
          val f = code(d, env)._1
          Eval(name.ofCode, s"$label, run by ${d.name}", s"$f$args = $tg", s"$f$args ≠ $tg")
        onPost.toList ++ onImpl.toList

    /** Under the first example's bindings, half at a boundary (a number of one input equal to one of another's). */
    private def probes: List[Eval] = n.cases.headOption.toList.flatMap { first =>
      val inputs = Probes.inputs(n.cases)
      // Without code to run, the post is judged on the examples' results.
      val calls = if impl.isDefined then inputs.map(ins => (ins, None))
        else inputs.flatMap(ins => n.cases.map(_.result).distinct.map(r => (ins, Some(r))))
      def edge(ins: List[Any]) = ins.map(Probes.numbers(_).toSet).combinations(2).exists(p => p(0).intersect(p(1)).nonEmpty)
      val (edges, rest) = scala.util.Random(n.id.hashCode).shuffle(calls).partition((ins, _) => edge(ins))
      // `x0 y0 x1 y1 …`, the longer list's rest at the end.
      val interleaved = edges.map(Some(_)).zipAll(rest.map(Some(_)), None, None).flatMap((x, y) => x.toList ++ y.toList)
      interleaved.iterator.zipWithIndex
        .flatMap { case ((ins, r), j) => one(ObligationName.Probe(j), s"probe ${j + 1}", first.bindings, ins, r).toOption }
        .filter(_.nonEmpty).take(Generate.ProbeCount).flatten.toList
    }

  // As `Lift` declares it: the owner chain without packages.
  private def leanName(c: Class[?]): String =
    val pkg = c.getPackageName
    val rest = if pkg.isEmpty then c.getName else c.getName.stripPrefix(pkg + ".")
    rest.replaceAll("[^$]*\\$package\\$", "").split('$').filter(_.nonEmpty).map(Names.ident).mkString(".")
  private def int(b: BigInt) = if b < 0 then s"($b)" else b.toString
  private def ctor(name: String, args: List[String]) = if args.isEmpty then s"$K.$name" else s"($K.$name ${args.mkString(" ")})"
  private def all(xs: Iterator[Any]): Option[List[String]] = xs.map(leanValue).toList.sequence
  private def lookup(pairs: List[(String, String)]): String =
    pairs.foldRight("none")((kv, rest) => s"if k' = ${kv._1} then some ${kv._2} else $rest")

  /** A run's outcome as Lean's `Except`: `Failed(e)` an error, anything else a result. */
  private def outcome(x: Any): Either[Any, Any] = x match
    case Failed(e) => Left(e)
    case r         => Right(r)

  private def leanValue(v: Any): Option[String] = v match
    case b: Boolean => Some(if b then "True" else "False")
    // The faults, where a boundary may fail: Lean's `List Bool`.
    case w: World   => w.parts.toList.sortBy(_._1.field).traverse((m, s) => leanValue(s).map(t => s"${m.field} := $t"))
      .map(fs => if kb.faulty then fs :+ s"faults := ${w.faults.mkString("[", ", ", "]")}" else fs)
      .map(fs => s"({ ${fs.mkString(", ")} } : $K.World)")
    case i: Int     => Some(int(BigInt(i)))
    case l: Long    => Some(int(BigInt(l)))
    case b: BigInt  => Some(int(b))
    case s: String  => Some(Names.string(s))
    case ()         => Some("()")
    case None       => Some("none")
    case Some(x)    => leanValue(x).map(t => s"(some $t)")
    case Left(x)    => leanValue(x).map(t => s"(Except.error $t)")
    case Failed(x)  => leanValue(x).map(t => s"(Except.error $t)")
    case Right(x)   => leanValue(x).map(t => s"(Except.ok $t)")
    case l: List[?] => all(l.iterator).map(_.mkString("[", ", ", "]"))
    // A map, as the function Lean has for it (see `Lift.tpe`); a set, as its membership.
    case m: Map[?, ?] => m.toList.traverse((k, v) => (leanValue(k), leanValue(v)).tupled).map(kvs => s"(fun k' => ${lookup(kvs)})")
    case st: Set[?] => all(st.iterator).map(xs => s"(fun y' => ${(xs.map(x => s"y' = $x") :+ "False").mkString(" ∨ ")})")
    case t: Product if t.getClass.getName.startsWith("scala.Tuple") => all(t.productIterator).map(_.mkString("(", ", ", ")"))
    case e: scala.reflect.Enum =>
      val c = if typeNames(leanName(e.getClass)) then e.getClass else e.getClass.getSuperclass
      Option.when(typeNames(leanName(c)))(leanName(c)).flatMap(t => all(e.productIterator).map(ctor(s"$t.${Names.ident(e.productPrefix)}", _)))
    case p: Product if typeNames(leanName(p.getClass)) => all(p.productIterator).map(ctor(s"${leanName(p.getClass)}.mk", _))
    case _ => None

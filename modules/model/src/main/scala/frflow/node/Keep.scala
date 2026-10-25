package frflow
package node

/** How a node stands to an invariant: kept, through a view of each call, or exempt. */
final case class Keep(invariant: Node[?], view: Option[Lifted[?]], exempt: String = ""):
  def describe: String = view.fold(s"${invariant.id}: exempt, because ${exempt}")(v => s"${invariant.id}: ${v.source}")

  // The casts are where the untyped IR meets the values: `keeps` built the view over the call and the rule over a pair.
  private[frflow] def brokenBy(inputs: List[Any], r: Any): Boolean =
    view.exists { v =>
      invariant.rule.exists { rl =>
        val rule = rl.value.asInstanceOf[(Any, Any) => Boolean]
        Fn.call(v.value, inputs :+ r).asInstanceOf[List[(Any, Any)]].exists((x, y) => !rule(x, y))
      }
    }

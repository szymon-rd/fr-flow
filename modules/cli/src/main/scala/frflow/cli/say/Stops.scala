package frflow.cli.say

import cats.syntax.all.*
import frflow.api.view.Stop

/** What stops a command, in words: each line the CLI prints on stderr. */
object Stops:
  def lines(s: Stop): List[String] = s match
    case Stop.Invalid(ps)                => ps.toList.map(p => s"error: ${Problems.text(p)}")
    case Stop.NoLean => List("no Lean: lake does not run (install elan; FRFLOW_LAKE names another " +
        "lake); render and status work without it")
    case Stop.UnknownNode(id)            => List(s"unknown node $id")
    case Stop.NotJson(file, problem)     => List(s"$file is not JSON: $problem")
    case Stop.NoVersion(file)            => List(s"$file has no version: it is not a file this FrFlow wrote")
    case Stop.UnknownVersion(f, v, r)    => List(s"$f is version $v; this FrFlow reads version $r")
    case Stop.BadField(f, v, field, p)   => List(s"$f (version $v): $field: $p")
    case Stop.NoKey(file)                => List(s"no signing key ($file): deciding needs the developer's key " +
        "(FRFLOW_KEY names it)")
    case Stop.NotAKey(file, problem)     => List(s"$file is not a signing key: $problem")

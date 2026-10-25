package frflow
package testing


/** The parts of a formula, or of a model's steps, a test must reach: an implication's premise, each side of an or, each
  * branch, each case of a match, and each list or option a `forall`/`exists` ranges over, not empty.
  */
private[frflow] object Coverage:
  def targets(root: Tree, print: Tree => String): List[(Tree, Int, String)] =
    def text(t: Tree) = { val s = print(t); if s.length > 120 then s.take(117) + "…" else s }
    def walk(t: Tree): List[(Tree, Int, String)] =
      val here = t match
        case Tree.Op(Prim.Implies, List(a, _)) => List((t, 1, s"${text(a)} held"))
        case Tree.Op(Prim.Or, List(a, b))      => List((t, 1, s"${text(a)} held"), (t, 2, s"${text(b)} held"))
        case Tree.If(c, _, _)                  => List((t, 1, s"${text(c)} held"), (t, 2, s"${text(c)} did not hold"))
        case Tree.Match(on, arms)              => arms.zipWithIndex.map((arm, i) => (t, i + 1, s"${text(on)} was ${pattern(arm.pat)}"))
        case Tree.Over(k, on, _, _) if Set(Iter.All, Iter.Some, Iter.OptAll, Iter.OptSome)(k) => List((t, 1, s"${text(on)} was not empty"))
        case _                                 => Nil
      here ++ children(t).flatMap(walk)
    walk(root)

  /** A model's steps: each branch taken either way, and the parts of the terms they compute. */
  def targets(s: Steps, print: Tree => String): List[(Tree, Int, String)] =
    val branches = Steps.fold(s, List.empty[(Tree, Int, String)]) {
      case (acc, Steps.Branch(c, _, _)) => acc ++ List((c, 1, s"${print(c)} held"), (c, 2, s"${print(c)} did not hold"))
      case (acc, _)                     => acc
    }
    branches ++ Trees.trees(s).flatMap(targets(_, print))

  private def pattern(p: Pat): String = p match
    case Pat.Ctor(_, c, _) => c.label
    case Pat.SomeP(_)      => "some value"
    case Pat.NoneP         => "none"
    case Pat.InjP(l, _)    => if l then "an error" else "a value"
    case Pat.ConsP(_, _)   => "not empty"
    case Pat.NilP          => "empty"

  private def children(t: Tree): List[Tree] = t match
    case Tree.Call(_, as)        => as
    case Tree.Apply(f, as)       => f :: as
    case Tree.Fun(_, b)          => List(b)
    case Tree.Quant(_, _, b)     => List(b)
    case Tree.If(c, a, b)        => List(c, a, b)
    case Tree.Match(on, arms)    => on :: arms.map(_.body)
    case Tree.Let(_, v, b)       => List(v, b)
    case Tree.Field(on, _, _)    => List(on)
    case Tree.Copy(on, _, us)    => on :: us.map(_._2)
    case Tree.Make(_, _, as)     => as
    case Tree.Tup(es)            => es
    case Tree.Proj(on, _, _)     => List(on)
    case Tree.SomeT(a)           => List(a)
    case Tree.Inj(_, a)          => List(a)
    case Tree.ListT(es)          => es
    case Tree.Over(_, on, _, b)  => List(on, b)
    case Tree.Op(_, as)          => as
    case _                       => Nil

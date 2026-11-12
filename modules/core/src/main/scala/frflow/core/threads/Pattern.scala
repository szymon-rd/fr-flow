package frflow.core.threads

/** What an arm of a `match` takes apart: a constructor over patterns, or a variable (`_` binds nothing). */
enum Pattern:
  case Ctor(name: String, args: List[Pattern])
  case Var(name: String)

  def bound: List[String] = this match
    case Ctor(_, args) => args.flatMap(_.bound)
    case Var("_")      => Nil
    case Var(n)        => List(n)

object Pattern:
  val Wild: Pattern = Var("_")
  def of(ctor: String, vars: String*): Pattern = Ctor(ctor, vars.toList.map(Var(_)))

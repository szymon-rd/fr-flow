package frflow.core.threads

/** What a function binds, as it is written: `(x : T)`; `x : T`, the one variable of a loop's function; or `x`,
  * its type left to Rocq (what a handler is given).
  */
enum Binder:
  case Typed(name: String, ty: Ty)
  case Bare(name: String, ty: Ty)
  case Plain(name: String)

  def bound: String = this match
    case Typed(n, _) => n
    case Bare(n, _)  => n
    case Plain(n)    => n

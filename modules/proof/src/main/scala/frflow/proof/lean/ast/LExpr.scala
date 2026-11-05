package frflow.proof.lean.ast

/** A Lean term as FrFlow writes them, no raw text. The lowering places every parenthesis and line of a `do` block,
  * so `Print` decides nothing.
  */
enum LExpr:
  case Name(name: LeanName)
  /** A qualified constant (`Crm.sameRows`, `FrFlow.within`, `Event.Expired`, `True`, `()`): each part an identifier. */
  case Const(path: List[LeanName])
  /** A constructor of a domain type, qualified by it (`Event.Expired`, `Booking.mk`): apart from every other constant,
    * so a field of one applied is read off its arguments by structure (`LeanTerm.field`), never by its spelling.
    */
  case Ctor(data: LeanName, ctor: LeanName)
  case Num(n: BigInt)
  case Str(s: String)
  case App(fn: LExpr, args: List[LExpr])
  case Infix(op: LOp, left: LExpr, right: LExpr)
  case Prefix(op: LPrefix, arg: LExpr)
  case Paren(inner: LExpr)
  /** `e.f`: a field (`t.store`), a model's part of a world (`after.database`), a projection (`.1`, `.2`). */
  case Dot(on: LExpr, field: String)
  case Tuple(elems: List[LExpr])
  case ListLit(elems: List[LExpr])
  /** `{ r with f := v, … }`. */
  case Update(record: LExpr, fields: List[(LeanName, LExpr)])
  case Fun(params: List[LBinder], body: LExpr)
  case Forall(params: List[LBinder], body: LExpr)
  case Exists(params: List[LBinder], body: LExpr)
  case If(cond: LExpr, ifTrue: LExpr, ifFalse: LExpr)
  case Match(on: LExpr, arms: List[(LExpr, LExpr)])
  case Let(name: LeanName, ty: LExpr, value: LExpr, body: LExpr)
  /** A `do` block: its lines start on the next line, at the given indentation. */
  case Do(lines: List[DoLine], indent: Int)
  /** `(e : T)`. */
  case Typed(e: LExpr, ty: LExpr)
  /** `⟨a, b, h⟩`: an anonymous constructor (the witnesses of an `∃`, then its proof). */
  case Anonymous(elems: List[LExpr])
  /** `by t`: a proof by one of FrFlow's own tactics, named (never built from a model). */
  case By(tactic: LeanName)
  /** `name (x := v)`: a named argument (`FrFlow.runOnE (ε := E) …`). */
  case Named(fn: LExpr, name: LeanName, value: LExpr)

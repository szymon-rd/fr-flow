package frflow.core.expr

/** An operator of the term language, one per meaning: an operator on several containers (`Contains` of a list, an
  * option or a set) is one, its operands' types telling which. Each has a Lean and a Scala meaning.
  */
enum PrimOp:
  case Eq, Ne, And, Or, Not, Implies
  case Add, Sub, Mul, Div, Mod, Lt, Le, Gt, Ge, Max, Min, Neg, Concat
  case Cons, Append, Nodup, Contains, IsEmpty, NonEmpty, Length, HeadOption, ToSet, Take, Drop, Zip
  /** `GetOrElse`: an option's value or a default; `GetOrElseAt`: a map's value at a key, or a default. */
  case Get, HasKey, GetOrElse, GetOrElseAt, Updated, Removed
  case Incl, Excl, Union, Intersect, SubsetOf

package frflow

/** An operator: how it prints and runs is in `LeanPrinter` and `Eval`. */
private[frflow] enum Prim:
  case Eq, Ne, And, Or, Not, Implies
  case Add, Sub, Mul, Div, Mod, Lt, Le, Gt, Ge, Max, Min, Neg, Concat
  case Cons, Append, Contains, IsEmpty, NonEmpty, Length, MapL, FoldLeft, FlatMap, HeadOption, ToSet, Take, Drop, Zip
  case Get, HasKey, GetOrElse, Updated, Removed
  case SetHas, Incl, Excl, Union, Intersect, SubsetOf
  case OptContains, IsDefined, OptIsEmpty, OptGetOrElse

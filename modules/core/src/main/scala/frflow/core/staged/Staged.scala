package frflow.core.staged

import frflow.core.code.Datum

/** The variables a function value, an argument by name or an object made inside a method keeps: each by its key,
  * then those of a scope the code was itself given (`rest`), if it was given one.
  */
final case class Kept(entries: List[(String, V)], rest: Option[String])

/** A value of staged code: a term of the prover of the machine's type of values. */
enum V:
  case Var(name: String)
  case Const(c: Datum)
  case Unit
  case Module(name: String)
  case Many(vs: List[V])
  /** A function made in the code: its definition, its unit's name in the place of its body, and the variables
    * it keeps.
    */
  case Function(stub: Datum, kept: Kept)
  /** An argument passed by name: the unit that evaluates it, and the variables it keeps. */
  case ByName(unit: Sym, kept: Kept)
  /** What a kept variable holds. */
  case Found(scope: String, key: String)

/** What an operation of staged code is given. */
enum Arg:
  case Val(v: V)
  case Vals(vs: List[V])
  case Text(s: String)
  case Name(s: Sym)
  case Type(t: Datum)
  case Types(ts: List[Datum])
  case Count(n: Int)
  case Prog(p: P)
  case Scope(k: Kept)
  /** The arguments of a call that takes some unevaluated: each a value kept for later, or a program run now. */
  case Lazily(args: List[Either[V, P]])

/** A handler of what a `try` catches: the names of what was thrown and of its value, and what is done. */
final case class Handler(thrown: String, value: String, body: P)

/** Staged code: a method as the sequence of the operations its tree means, each named by the function of
  * `FrFlow/Scala/Staged.v` that does it. What the meaning looks up in the tree and in the scope is looked up
  * here, once; what it decides of values when the code runs is left to those functions.
  */
enum P:
  case Give(v: V)
  case Bind(name: String, of: P, next: P)
  case Let(name: String, v: V, next: P)
  case Op(name: String, args: List[Arg])
  /** By a truth value: one program or the other. */
  case Truth(test: V, yes: P, no: P)
  /** By what a pattern's parts are, if the value has them: named, then `found`; else `missed`. */
  case Parts(of: P, names: List[String], found: P, missed: P)
  /** `p` under a name, used where the name is. */
  case Share(name: String, p: P, next: P)
  case Use(name: String)
  case Stuck(why: String)
  /** What a method is given, named. */
  case Given(names: List[String], body: P)
  case Handle(body: P, handler: Option[Handler], last: Option[P])

/** What `bodies` answers a call with: a method by its definition, an initialiser by its class, a function and
  * an argument by name by the unit's name that the value holds.
  */
enum UnitKind:
  case Method(s: Sym)
  case Init(cls: String)
  case Function(s: Sym)
  case ByName(s: Sym)

/** One program of staged code. A method and an initialiser are given the object and the arguments; a function
  * the variables it keeps and the arguments; an argument by name the variables it keeps.
  */
final case class StagedUnit(kind: UnitKind, name: String, body: P)

/** The staged code of some files: every unit that could be staged; of each that could not, why; and the
  * definitions from outside the units call, each with the arguments the staging took it to take unevaluated.
  */
final case class StagedCode(
    units: List[StagedUnit], unstaged: List[(String, String)], outside: List[(Sym, List[Boolean])])

package frflow.core.normal

import frflow.core.effect.{ClassName, EType, FieldName, MethodName, OutsideName, Prim}

/** A local of a method, by the name the code gives it (or the reading, for an intermediate result) and a number
  * no other local of the method has.
  */
final case class Local(name: String, id: Int)

/** What an operation is given: a local, a literal, or the object the method is called on. Evaluating one does
  * nothing.
  */
enum Atom:
  case Of(local: Local)
  case Whole(value: BigInt)
  case Truth(value: Boolean)
  case Nothing
  case NoObject
  case Self

/** How a call finds what it runs: a method of the code read, or a member outside it. */
enum Kind:
  case Static(method: MethodName)
  case External(member: OutsideName)

/** What a `val` is bound to: an atom as it is now (a copy of a `var`), one operation on atoms, or a choice
  * between two blocks.
  */
enum Rhs:
  case Is(atom: Atom)
  case Applied(op: Prim, args: List[Atom])
  case Read(on: Atom, field: FieldName)
  case Make(cls: ClassName)
  case Call(kind: Kind, on: Atom, args: List[Atom])
  case Choice(test: Atom, yes: Block, no: Block)

/** A statement. `Val` binds a local once; `temp` says the reading introduced it for an intermediate result, the
  * code did not name it. `Var` declares a local that `Assign` gives a new value. `Run` evaluates and drops the
  * value.
  */
enum Stmt:
  case Val(local: Local, ty: EType, rhs: Rhs, temp: Boolean)
  case Var(local: Local, ty: EType, start: Atom)
  case Assign(local: Local, value: Atom)
  case Write(on: Atom, field: FieldName, value: Atom)
  case Loop(test: Block, body: Block)
  case Run(rhs: Rhs)

/** Statements in order, and the value the block gives. */
final case class Block(stmts: List[Stmt], gives: Atom)

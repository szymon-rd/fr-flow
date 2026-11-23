package frflow.core.effect

/** One effect of code read, typed by what it gives (`FrFlow/Effect/Sig.v`): a field read or written, an object
  * made, a method of the code called on an object, something outside the code called.
  */
enum Effect:
  case Get(on: Pure, field: FieldName)
  case Put(on: Pure, field: FieldName, value: Pure)
  case New(cls: ClassName)
  case Call(method: MethodName, on: Pure, to: List[Pure])
  case Ext(member: OutsideName, to: List[Pure])

/** Code as a tree of effects (`FrFlow/Effect/Tree.v`): it gives a value; or does an effect and goes on, what the
  * effect gave named or not; or names a value; or goes one of two ways; or runs a tree and goes on with what it
  * gave, named part by part; or loops over a state and goes on with the state it left with. `Again` and `Leave`
  * end a turn of a loop's body: with the next state, or with the state the loop leaves with.
  */
enum Tree:
  case Give(value: Pure)
  case Do(named: Option[String], effect: Effect, next: Tree)
  case Name(name: String, value: Pure, next: Tree)
  case Branch(test: Pure, yes: Tree, no: Tree)
  case After(first: Tree, named: List[String], next: Tree)
  case Loop(state: List[String], start: List[Pure], body: Tree, next: Tree)
  case Again(state: List[Pure])
  case Leave(state: List[Pure])

object Tree:
  /** The same tree with what says nothing removed: a tree run only to give what it gave is that tree. */
  def simplified(t: Tree): Tree = t match
    case After(first, List(x), Give(Pure.Local(y))) if x == y => simplified(first)
    case After(first, named, next)                           => After(simplified(first), named, simplified(next))
    case Do(named, effect, next)                             => Do(named, effect, simplified(next))
    case Name(name, value, next)                             => Name(name, value, simplified(next))
    case Branch(test, yes, no)                               => Branch(test, simplified(yes), simplified(no))
    case Loop(state, start, body, next)                      => Loop(state, start, simplified(body), simplified(next))
    case other                                               => other

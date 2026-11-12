package frflow.core.threads

/** A unit of code as it is read, before it is laid out as a file (`Assemble`): its types in the order they are
  * declared; its definitions by group, in the order of the source, their closures still in place (`Term.Closure`);
  * what those definitions may mention (`support`); the type of the capabilities a closure of the caller's holds
  * (`holds`); and what was not read, which is `chaos` in the definitions (`unread`).
  */
final case class Draft(types: List[Decl], groups: List[Draft.Group], support: Support, holds: Ty,
    unread: List[Draft.Unread])

object Draft:
  /** A definition read, and the name its closures are named after: its method's, whichever overload it is. */
  final case class Read(base: String, definition: Decl.Definition)

  /** Code that is not read: what `chaos` is named for, and the construct the reader refused. */
  final case class Unread(what: String, why: String)

  /** The definitions read of one class, or of one file's top level, under a heading. */
  final case class Group(title: String, defs: List[Read])

package frflow.dsl.compiled.threads.known

/** The unit of code a thread program is read from: a table of names, given to the reader (`ReadThreads`).
  *
  *   - `types`: the classes read as types, in the order they are declared, each after those its fields are of;
  *   - `groups`: the definitions read, by heading;
  *   - `opaque`: the classes not read: a value of one is a handle, a call of one `extern`;
  *   - `holds`: the class of the capabilities a closure of the caller's may hold.
  */
final case class ThreadUnit(types: List[ThreadUnit.Kind], groups: List[ThreadUnit.Group], opaque: List[String],
    holds: String)

object ThreadUnit:
  /** A class read as a type. */
  enum Kind:
    /** A class: the record of its fields. */
    case Class(name: String)
    /** A trait: the sum of the cases named, or of its children when it is sealed and none is named. */
    case Sum(name: String, cases: List[String])

  /** The definitions written under one heading. */
  final case class Group(title: String, members: List[Member])

  /** What a group reads. */
  enum Member:
    /** A class's constructor and every method it declares. */
    case Whole(owner: String)
    /** Every method an object declares. */
    case Object(owner: String)
    /** The methods named `name` that a class or its companion declares, as written in the source. */
    case Of(owner: String, name: String)
    /** The top-level methods named `name` of a package. */
    case TopLevel(pkg: String, name: String)
    /** For each method a sum declares, the function that calls the case's. */
    case Dispatch(sum: String)

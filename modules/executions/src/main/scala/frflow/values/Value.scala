package frflow.values

import frflow.*

// What code handles, as a statement about an execution speaks of it: one type for every piece of data and every
// reference to an object, since a call is made with any of them and responds with any of them.

/** A value of the code: a piece of data, or a reference to an object. */
enum Value derives RocqType:
  case Unit
  case Bool(value: Boolean)
  case Int(value: BigInt)
  case Str(value: String)
  case Reference(address: BigInt)
  /** What the JDK throws, known by its class alone: an execution does not tell two of one class apart. */
  case Thrown(cls: String)
  /** No object: `null`. */
  case Null

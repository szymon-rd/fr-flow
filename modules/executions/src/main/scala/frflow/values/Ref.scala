package frflow.values

import frflow.*

/** An object of class `C`, as a statement names it: which object, not what is in it. */
opaque type Ref[C] = Value

object Ref:
  given [C]: RocqType[Ref[C]] = summon[RocqType[Value]].asInstanceOf[RocqType[Ref[C]]]

  extension [C](r: Term[Ref[C]])
    /** The object as a value of the code. */
    def asValue: Term[Value] = r.asInstanceOf[Term[Value]]

    /** The same object, named as one of class `D`: a set of threads as a set of objects. */
    def seenAs[D]: Term[Ref[D]] = r.asInstanceOf[Term[Ref[D]]]

/** An object of class `C` in a statement. */
type Obj[C] = Term[Ref[C]]

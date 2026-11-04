package frflow.core.code

import frflow.core.name.CtorName

/** How Scala builds and takes apart the values of a domain type. A handle on Scala: never compared or printed. */
final class DataRep(val make: (CtorName, List[Any]) => Any, val split: Any => (CtorName, List[Any]))

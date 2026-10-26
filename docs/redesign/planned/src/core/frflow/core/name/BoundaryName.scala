package frflow.core.name

/** A boundary's name (`database`): what proven flows call but cannot see. */
opaque type BoundaryName = String

object BoundaryName extends Label[BoundaryName]

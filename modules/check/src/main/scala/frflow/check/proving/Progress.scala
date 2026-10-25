package frflow
package check
package proving

/** How far a check is: Lean is about to build the models (`level` 0), or to prove level `level` of `levels`. */
final case class Progress(level: Int, levels: Int, nodes: List[String])

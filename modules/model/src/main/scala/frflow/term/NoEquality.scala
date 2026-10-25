package frflow
package term

import scala.annotation.implicitNotFound

@implicitNotFound("FrFlow: compare terms with === (and =!=), not == (which compares the trees); in plain code, compare values (`d.fn(…)`, `p.value`)")
sealed trait NoEquality

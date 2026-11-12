package frflow.proof.obligation

import frflow.core.analysis.resolution.{Callees, Resolved}
import frflow.core.code.Code
import frflow.core.name.SymbolName

/** The fixed values (`defineValue`) among `symbols` and what the proven code standing for them reaches, each
  * standing as its value: a claim mentioning a fixed Definition is stated for that value (2.7).
  */
object Fixed:
  def of(r: Resolved, symbols: Iterable[SymbolName]): Map[SymbolName, Substitute] =
    Callees.reaching(r.theory, symbols.toList.distinct).flatMap(s => r.theory.code.attached.get(s).map(_.code)
      .collect { case Code.Valued(v) => s -> Substitute.Fixed(Constant(v, Required.typeOf(r, s).getOrElse(
        throw IllegalStateException(s"FrFlow bug: the fixed value ${s.value} has no type")))) }).toMap

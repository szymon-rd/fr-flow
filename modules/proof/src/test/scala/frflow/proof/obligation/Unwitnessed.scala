package frflow.proof.obligation

import frflow.core.{Kb, Lang}
import frflow.core.Nodes.*
import frflow.core.analysis.{Resolve, Resolved, Validate}
import frflow.core.ty.Ty

/** `allowsOne` from a part no equation solves: its group of consistency is not witnessed. */
object Unwitnessed:
  private val test = Ty.FnOf(List(Lang.big), Ty.Bool)
  private def allowed[T[_]](l: Lang[T], n: T[BigInt]): T[Boolean] =
    l.call(l.sym[BigInt => Boolean]("allowed", test), n)
  val resolved: Resolved = Resolve(Validate(Kb.of(
    claim("allowsOne")(Lang.formula([T[_]] => (l: Lang[T]) => allowed(l, l.num(1)))),
    claim("grows")(Lang.formula([T[_]] => (l: Lang[T]) => l.forall[BigInt]("n", Lang.big)(n =>
      l.s.implies(allowed(l, n), allowed(l, l.s.add(n, l.num(1))))))))
    .naming(declaration("allowed", test)).linking(partOf("grows", "allowsOne")).elaborated)
    .fold(ps => throw IllegalStateException(ps.toString), identity))

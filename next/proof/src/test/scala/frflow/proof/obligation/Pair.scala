package frflow.proof.obligation

import frflow.core.{Kb, Lang}
import frflow.core.Nodes.*
import frflow.core.analysis.{Resolve, Resolved, Validate}
import frflow.core.ty.Ty

/** Two Declarations and the claims that try every try: `both` (`f 1 ∧ g 2`) split into one part per conjunct (each
  * needed, each restating a conjunct, the parts clashing, nothing meeting it, doing nothing), and `same`, which its
  * one part restates.
  */
object Pair:
  private val test = Ty.FnOf(List(Lang.big), Ty.Bool)
  private def call[T[_]](l: Lang[T], f: String, n: T[BigInt]): T[Boolean] = l.call(l.sym[BigInt => Boolean](f, test), n)
  private def about(name: String, f: String)(rule: [T[_]] => (Lang[T], T[BigInt]) => T[Boolean]) =
    claim(name)(Lang.formula([T[_]] => (l: Lang[T]) =>
      l.forall[BigInt]("n", Lang.big)(n => l.s.eq(call(l, f, n), rule[T](l, n)))))

  val kb: Kb = Kb.of(
    claim("both")(Lang.formula([T[_]] => (l: Lang[T]) => l.s.and(call(l, "f", l.num(1)), call(l, "g", l.num(2))))),
    about("aboutF", "f")([T[_]] => (l: Lang[T], n: T[BigInt]) => l.s.lt(l.num(0), n)),
    about("aboutG", "g")([T[_]] => (l: Lang[T], n: T[BigInt]) => l.s.lt(n, l.num(3))),
    about("same", "f")([T[_]] => (l: Lang[T], n: T[BigInt]) => l.s.lt(l.num(0), n)))
    .naming(declaration("f", test), declaration("g", test))
    .linking(partOf("aboutF", "both"), partOf("aboutG", "both"), partOf("aboutF", "same"))

  lazy val resolved: Resolved = Resolve(Validate(kb.elaborated).fold(ps => throw IllegalStateException(ps.toString),
    identity))

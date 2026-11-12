package frflow.eval.assumed

import cats.effect.{IO, Ref}
import frflow.*

/** The step 13c review's B1, small: a draw known only by assumptions, said to be fresh against the register, another
  * model. Its runs are of its own model's state alone in Lean, so the assumption would be said of every register beside
  * every state of the drawer (`ReadsBeside`); handed the register's numbers as an input, it is said of them.
  */
object Beside:
  import Lookup.{put, has, register, hasKeeps, registerOnly}

  val draw = Declaration[Flow[BigInt]]("a number drawn from outside")
  val drawAgainst = Declaration[List[BigInt] => Flow[BigInt]]("a number drawn from outside, none of those given")
  object drawer extends StateModel[BigInt]("how many numbers were drawn"):
    draw.assumed
    drawAgainst.assumed

  val drawKeeps = Node.assumption("Drawing changes nothing.")(drawer.in(draw.after) === drawer.current)
  val drawnFresh = Node.assumption("A number drawn is none the register holds.")(
    !register.current.contains(draw.result))
  val drawnApart = Node.assumption("A number drawn against some is none of them.")(
    forall((xs: Term[List[BigInt]]) => !xs.contains(drawAgainst(xs).result)))
  val drawnAgainstKeeps = Node.assumption("Drawing against some changes nothing.")(
    forall((xs: Term[List[BigInt]]) => drawer.in(drawAgainst(xs).after) === drawer.current))

  final class Drawer(r: Ref[IO, BigInt]):
    def draw: IO[BigInt] = r.get
    def drawAgainst(xs: List[BigInt]): IO[BigInt] = IO.pure(xs.maxOption.fold(BigInt(0))(_ + 1))
    def drawn: IO[BigInt] = r.get

  private def kb(nodes: Node*): FrModel = FrModel("Beside")(nodes*)
    .defining(defineOperations(put, has)(start = Lookup.Indexed.holding(_), observe = _.numbers)(i => (i.put, i.has)))
    .defining(defineOperations(draw, drawAgainst)(start = (n: BigInt) => Ref[IO].of(n).map(Drawer(_)),
      observe = _.drawn)(
      d => (d.draw, d.drawAgainst)))

  /** What a claim can say of it, handed the register's numbers: proven from what is assumed of it. */
  val drawnNew = Node.claim("A number drawn against the register's numbers is none of them.")(
    !register.current.contains(drawAgainst(register.current).result))

  /** Fresh against the register: refused. */
  val reading: FrModel = kb(drawnNew, drawnFresh, drawKeeps, drawnApart, drawnAgainstKeeps, hasKeeps, registerOnly)
  /** Fresh against what it is handed: valid. */
  val handed: FrModel = kb(drawnNew, drawKeeps, drawnApart, drawnAgainstKeeps, hasKeeps, registerOnly)

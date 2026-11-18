package frflow.dsl.structure

import frflow.core.expr.Expr
import frflow.dsl.kb.FrModel
import frflow.dsl.kb.Defining.*
import frflow.dsl.compiled.steps.ClassSyntax.lifted
import frflow.dsl.node.Node
import frflow.dsl.term.Term
import frflow.dsl.term.TermSyntax.*
import frflow.dsl.structure.Declaring as Declaration
import scala.annotation.experimental

/** The shorthands of a call (`following`, `again`, `andThen`, `changesNothing`, `unchangedBy`, `isIdempotent`): each
  * claim written with one says what the claim written out with `in` and `after` says, term for term.
  */
@experimental class ShorthandSuite extends munit.FunSuite:
  import ShorthandSuite.{Long, Short}

  private def formulas(model: FrModel): Map[String, Expr] =
    model.elaborated.fold(es => fail(es.toChain.toList.mkString("; ")), identity).theory.nodes
      .flatMap(n => n.node.statement.said.map(n.node.id.value -> _.value)).toMap

  test("each shorthand gives the formula written out with in and after") {
    val (short, long) = (formulas(Short.model), formulas(Long.model))
    assertEquals(short.keySet, Set("followed", "twice", "chained", "still", "unmoved", "idempotent"))
    short.foreach((id, formula) => assertEquals(formula, long(id), id))
  }

@experimental object ShorthandSuite:
  import Till.{CashTill, Sale, Till}

  /** The claims written with the shorthands. */
  object Short:
    val till = Declaration[Till]("the till")
    val followed = Node.claim("A sale taken is recorded.")(
      forall((s: Term[Sale]) => till.taken(s.id).following(till.take(s))))
    val twice = Node.claim("A sale taken twice is refused the second time.")(
      forall((s: Term[Sale]) => !till.take(s).again.result))
    val chained = Node.claim("What taking a sale answers is whether it is taken after.")(
      forall((s: Term[Sale]) => till.take(s).andThen(_ => till.taken(s.id)) === till.take(s).result))
    val still = Node.claim("Reading the total changes nothing.")(till.total.changesNothing)
    val unmoved = Node.claim("Taking a sale already taken leaves the count as it was.")(
      forall((s: Term[Sale]) => till.taken(s.id) implies till.count.unchangedBy(till.take(s))))
    val idempotent = Node.claim("Taking a sale is idempotent.")(
      forall((s: Term[Sale]) => till.take(s).isIdempotent))
    val model: FrModel = FrModel("Tills")(followed, twice, chained, still, unmoved, idempotent)
      .defining(till.define(lifted[CashTill]))

  /** The same claims written out with `in` and `after`. */
  object Long:
    val till = Declaration[Till]("the till")
    val followed = Node.claim("A sale taken is recorded.")(
      forall((s: Term[Sale]) => till.taken(s.id).in(till.take(s).after)))
    val twice = Node.claim("A sale taken twice is refused the second time.")(
      forall((s: Term[Sale]) => !till.take(s).in(till.take(s).after).result))
    val chained = Node.claim("What taking a sale answers is whether it is taken after.")(
      forall((s: Term[Sale]) => till.taken(s.id).in(till.take(s).after) === till.take(s).result))
    val still = Node.claim("Reading the total changes nothing.")(till.total.after === till.current)
    val unmoved = Node.claim("Taking a sale already taken leaves the count as it was.")(
      forall((s: Term[Sale]) => till.taken(s.id) implies (till.count.in(till.take(s).after) === till.count)))
    val idempotent = Node.claim("Taking a sale is idempotent.")(
      forall((s: Term[Sale]) => (till.take(s).in(till.take(s).after) === till.take(s)) &&
        (till.take(s).in(till.take(s).after).after === till.take(s).after)))
    val model: FrModel = FrModel("Tills")(followed, twice, chained, still, unmoved, idempotent)
      .defining(till.define(lifted[CashTill]))

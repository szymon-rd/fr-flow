package frflow.eval

import cats.effect.IO
import frflow.*
import frflow.core.Elaborated
import frflow.core.analysis.{Resolve, Validate}
import frflow.core.expr.Binder
import frflow.core.spec.{Form, Written}
import frflow.core.term.Final
import frflow.core.ty.Ty
import frflow.proof.layout.Laid
import frflow.proof.lean.ast.{Decl, ModuleName}
import frflow.proof.lean.laws.DoBlocks
import frflow.proof.lean.print.Print

/** A count replaced, the old one given; its parameter named `s`, as the back end once named the state beside it. */
val keep = Definition[BigInt => Program[BigInt]]("the count replaced, the old one given")
object tally extends StateModel[BigInt]("a count"):
  keep.means(s => state.get.flatMap(old => state.set(s).map(_ => old)))

/** No name the back end writes itself captures an operation's or a define's parameter (the review's probe: `def
  * keep_of (s : Int) (s : Int)`, whose `made_` was stated of the state run on itself): every port's Lean, each model
  * operation's and define's parameters all renamed to a name the back end binds (`s`, `w`, `x`, `k`, …), a namespace
  * or a name Lean writes itself, reads as it does unrenamed, up to the names of its variables (`DoBlocks`).
  */
class ParamsCaptureSuite extends munit.FunSuite:
  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(5, "minutes")
  private val names = List("s", "w", "x", "x0", "x1", "x_1", "k", "y", "m", "init", "h_x", "some", "by", "World",
    "pure", "Ops", "FrFlow", "Except")
  private def elaborated(kb: FrModel): Elaborated = kb.elaborated.fold(es => fail(es.iterator.mkString), identity)

  private def renamed(e: Elaborated, to: String): Elaborated =
    val v = e.theory.vocabulary
    def ps(xs: List[Binder]) = xs.map(_.copy(hint = to))
    val models = v.models.map(m => m.copy(ops = m.ops.map(o => o.copy(params = ps(o.params)))))
    val defines = v.defines.map(d => d.copy(written = d.written.form match
      case Form.Term(t)  => Written.lambda(ps(d.lambda.params), t.run.asInstanceOf[Final[Any]], d.written.source)
      case Form.Steps(p) => Written.steps(ps(d.lambda.params), p, Ty.yields(d.lambda.result), d.written.source)))
    e.copy(theory = e.theory.copy(vocabulary = v.copy(models = models, defines = defines)))

  private def modules(e: Elaborated): List[(ModuleName, List[Decl])] =
    Laid(Resolve(Validate(e).fold(ps => fail(ps.toString), identity)), Map.empty, Nil).modules
      .map(m => m.name -> m.decls.map(DoBlocks.decl))

  private val tallied = FrModel("Tallies")(Node.claim("Replacing gives the old count.")(
    forall((x: Term[BigInt], now: Term[World]) => keep(x).from(now) { (old, _) => old === tally.in(now) })))
    .implementTested(keep)(start = (n: BigInt) => IO(Counter(n)), observe = (t: Counter) => IO(t.n))(t =>
      Tuple1(t.keep))

  test("an operation's parameter named s is apart from the state its result is run on: keep_of (s) (s_1)") {
    val printed = Laid(Resolve(Validate(elaborated(tallied)).toOption.get), Map.empty, Nil).modules
      .map(Print.module).mkString("\n")
    assert(printed.contains("def keep_of (s : Int) (s_1 : Int) : Int :=\n  Id.run ((Tally.keep s).run' s_1)"),
      printed.linesIterator.filter(_.contains("keep")).mkString("\n"))
  }

  List("tallies" -> tallied, "rooms" -> rooms.rooms, "auth" -> auth.knowledge, "crm" -> crm.knowledge,
    "keycloak" -> keycloak.knowledge).foreach { (name, kb) =>
    test(s"$name: every parameter renamed, to a name the back end binds or writes, its Lean reads the same") {
      val e = elaborated(kb)
      val base = modules(e)
      val more = (e.theory.name.value :: e.theory.vocabulary.models.map(_.name.value.capitalize))
      (names ++ more).foreach(to => assertEquals(modules(renamed(e, to)), base, to))
    }
  }

/** The tally's plain Scala. */
final class Counter(var n: BigInt):
  def keep(x: BigInt): IO[BigInt] = IO { val o = n; n = x; o }

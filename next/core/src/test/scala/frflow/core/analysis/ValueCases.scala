package frflow.core.analysis

import frflow.core.{Kb, Lang, Store}
import frflow.core.Nodes.*
import frflow.core.code.Code
import frflow.core.expr.{Binder, Value}
import frflow.core.name.{DefName, NodeId, SourceText, SymbolName, TypeName, VarId}
import frflow.core.spec.Written
import frflow.core.term.{Final, Sym}
import frflow.core.ty.Ty
import frflow.core.vocab.{Define, DefineForm, Sort}

/** One theory per problem of the vocabulary and of the two kinds of values. */
object ValueCases:
  private def id(s: String) = NodeId(s)
  private def name(s: String) = SymbolName(s)
  private val root = plain("root")
  private val test = Ty.FnOf(List(Lang.big), Ty.Bool)

  /** `∀ x, d(x)`. */
  def holdsOf(id: String, d: String): frflow.core.spec.Node = claim(id)(Lang.formula([T[_]] => (l: Lang[T]) =>
    l.forall[BigInt]("x", Lang.big)(x => l.call(l.sym[BigInt => Boolean](d, test), x))))

  /** A define over one number calling the symbol `d` on it. */
  def calling(define: String, d: String): Define =
    val x = Binder(VarId.level(0), "x", Lang.big)
    val body: Final[Boolean] = [T[_]] => (s: Sym[T]) => s.app(s.param[BigInt => Boolean](name(d), test), s.free(x))
    Define(DefName(define), Written.lambda(List(x), body, SourceText(define)), DefineForm.Function)

  private val connected = claim("connected")(Lang.formula([T[_]] => (l: Lang[T]) =>
    l.s.eq(l.sym[String]("connection", Ty.Str), l.str("db"))))

  /** `top` is proven of `grant`'s code, which calls `free`, from a part about `free` and one about nothing. */
  val proven: Kb = Kb.of(holdsOf("top", "granted"), holdsOf("aboutFree", "free"), plain("stray"))
    .naming(definition("granted", test), definition("free", test))
    .declaring(_.copy(defines = List(calling("grant", "free"))))
    .coding(name("granted") -> Code.Proven(DefName("grant")), name("free") -> Code.Provided)
    .linking(partOf("aboutFree", "top"), partOf("stray", "top"))

  /** `f`'s code calls `g` and `g`'s calls `f`: the claim on each rests on the claim on the other. */
  val mutual: Kb = Kb.of(holdsOf("aboutF", "f"), holdsOf("aboutG", "g"))
    .naming(definition("f", test), definition("g", test))
    .declaring(_.copy(defines = List(calling("fCode", "g"), calling("gCode", "f"))))
    .coding(name("f") -> Code.Proven(DefName("fCode")), name("g") -> Code.Proven(DefName("gCode")))

  /** `∀ x, inc(x) ∧ f(x)`: a claim on `f`, whose code calls `inc`, and on `inc` too. */
  def above(id: String): frflow.core.spec.Node = claim(id)(Lang.formula([T[_]] => (l: Lang[T]) =>
    l.forall[BigInt]("x", Lang.big)(x => l.s.and(l.call(l.sym[BigInt => Boolean]("inc", test), x),
      l.call(l.sym[BigInt => Boolean]("f", test), x)))))

  /** Two such claims about the same code, siblings: neither is a fact about a callee of the other's code. */
  val siblings: Kb = Kb.of(above("fAbove"), above("fAboveToo"))
    .naming(definition("f", test), definition("inc", test))
    .declaring(_.copy(defines = List(calling("fCode", "inc"))))
    .coding(name("f") -> Code.Proven(DefName("fCode")), name("inc") -> Code.Provided)

  private val int = Ty.Num(frflow.core.ty.NumKind.Int32)
  /** `¬ ∀ (x : Int), x = x`: a Scala `Int` said to exist. */
  private val notAll = claim("notAll")(Lang.formula([T[_]] => (l: Lang[T]) =>
    l.s.not(l.forall[Int]("x", int)(x => l.s.eq(x, x)))))

  val all: List[ProblemCase] = List(
    ProblemCase(Kb.of(notAll).naming(declaration("count", Ty.ListOf(int))),
      List(Problem.SaidToExist(int, Problem.Place.Variable(id("notAll"))),
        Problem.SaidToExist(Ty.ListOf(int), Problem.Place.Value("count")))),
    ProblemCase(mutual, List(Problem.RestsOnItself(List(id("aboutF"), id("aboutG"))))),
    ProblemCase(Kb.of(root).naming(declaration("get", test))
      .declaring(v => v.copy(sorts = List(Sort(TypeName("World"), "a world")), defines = List(calling("Obl", "get")),
        models = List(Store.stateModel.copy(name = frflow.core.name.ModelName("stateM"))))),
      List(Problem.ReservedName("World"), Problem.ReservedName("get"), Problem.ReservedName("Obl"),
        Problem.ReservedName("StateM"))),
    ProblemCase(Kb.of(root).naming(declaration("access", test), declaration("access", test)),
      List(Problem.DeclaredTwice("access"))),
    ProblemCase(Kb.of(connected).naming(codeOnly("connection")).coding(name("connection") -> Code.Provided),
      List(Problem.CodeOnlyInStatement(id("connected"), name("connection"), "Connection"))),
    ProblemCase(Kb.of(root).naming(definition("granted", test)), List(Problem.Undefined(name("granted")))),
    ProblemCase(Kb.of(holdsOf("admits", "admitted")).naming(declaration("allowed", test), definition("admitted", test))
      .declaring(_.copy(defines = List(calling("admit", "allowed"))))
      .coding(name("admitted") -> Code.Proven(DefName("admit"))),
      List(Problem.DeclarationInCode(DefName("admit"), name("allowed")))),
    ProblemCase(Kb.of(root).naming(definition("limit", Lang.big)).coding(name("limit") -> Code.Valued(Value.Num(3))),
      List(Problem.CodeWithoutClaim(name("limit")))))

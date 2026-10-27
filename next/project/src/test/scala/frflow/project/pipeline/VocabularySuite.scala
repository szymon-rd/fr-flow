package frflow.project.pipeline

import cats.data.NonEmptyList
import frflow.core.code.CodeTable
import frflow.core.name.*
import frflow.core.{Sited, Theory}
import frflow.core.spec.{Node, Reliance, Statement, Written}
import frflow.core.term.{Bound, Final, Sym}
import frflow.core.ty.{Ctor, DataType, Field, Ty}
import frflow.core.vocab.{Sort, Symbol, SymbolType, ValueKind, Vocabulary}

/** The rule of the `vocabulary` field, on an excerpt of auth's ledger (`examples/auth/.frflow/ledger.json`) built by
  * hand: a definition lists the term it defines with the terms its body mentions; a claim lists the opaque types its
  * terms are over. The pin that today's field is reproduced is step 0's `GoldenExamplesSuite`, over all four ledgers.
  */
class VocabularySuite extends munit.FunSuite:
  private val userId = Ty.Data(TypeName("UserId"))
  private val path = Ty.Data(TypeName("Path"))
  private val grant = Ty.Data(TypeName("Grant"))
  private val (user, resource) = (Ty.Sort(TypeName("User")), Ty.Sort(TypeName("Resource")))
  private def symbol(n: String, means: String, ty: Ty) =
    Symbol(SymbolName(n), means, SymbolType.Typed(ty), ValueKind.Definition)
  private val authorizedMeans = "whether the user is allowed the resource, by whatever rule the system adopts"
  private val grantsMeans = "the grant table as stored when the request is decided"
  private val accessMeans = "whether the system lets the user access the resource"

  private val vocabulary = Vocabulary(
    List(Sort(TypeName("User"), "a person who uses the system"),
      Sort(TypeName("Resource"), "something a user may want to access")),
    List(DataType.Product(TypeName("Grant"), "Grant", List(Field("user", userId), Field("path", path))),
      DataType.Sum(TypeName("UserId"), "UserId", NonEmptyList.one(Ctor(CtorName("mk"), Nil)))),
    List(symbol("authorized", authorizedMeans, Ty.FnOf(List(user, resource), Ty.Bool)),
      symbol("grants", grantsMeans, Ty.ListOf(grant)),
      symbol("access", accessMeans, Ty.FnOf(List(user, resource), Ty.Bool))),
    Nil, Nil, Nil)

  /** A claim over `access`, whose type names both opaque types. */
  private val accessExactly =
    val access = SymbolName("access")
    val claim: Final[Boolean] = [T[_]] => (s: Sym[T]) => s.forall(Bound[Any]("u", user))(u =>
      s.forall(Bound[Any]("r", resource))(r =>
        s.app(s.app(s.param[Any => Any => Boolean](access, Ty.FnOf(List(user, resource), Ty.Bool)), u), r)))
    Node(NodeId("AccessExactly"), "…",
      Statement.Claim(Written.formula(claim, SourceText("…")), Reliance.Relied))

  private val theory = Theory(KbName("Auth"), vocabulary,
    List(accessExactly).map(Sited(_, Span(RelPath.fromIdentifiers("src", "Auth.scala"), 0))), Nil,
    CodeTable(Map.empty, Map.empty))

  test("a claim's vocabulary has the opaque types its terms are over (AccessExactly, in part)") {
    assertEquals(Texts.vocabulary(theory, NodeId("AccessExactly")),
      List("Resource: something a user may want to access", "User: a person who uses the system",
        s"access: $accessMeans"))
  }

package frflow.project.pipeline

import cats.data.NonEmptyList
import frflow.core.code.CodeTable
import frflow.core.expr.{Binder, Expr, Lambda, PrimOp}
import frflow.core.name.*
import frflow.core.{Sited, Theory}
import frflow.core.spec.{Fixing, Node, Prose, Statement, Written}
import frflow.core.ty.{Ctor, DataType, Field, Ty}
import frflow.core.vocab.{Sort, Symbol, SymbolType, Vocabulary}

/** The rule of the `vocabulary` field, on an excerpt of auth's ledger (`examples/auth/.frflow/ledger.json`) built by
  * hand: a definition lists the term it defines with the terms its body mentions; a claim lists the opaque types its
  * terms are over. The pin that today's field is reproduced is step 0's `GoldenExamplesSuite`, over all four ledgers.
  */
class VocabularySuite extends munit.FunSuite:
  private val userId = Ty.Data(TypeName("UserId"))
  private val path = Ty.Data(TypeName("Path"))
  private val grant = Ty.Data(TypeName("Grant"))
  private val (user, resource) = (Ty.Sort(TypeName("User")), Ty.Sort(TypeName("Resource")))
  private def symbol(n: String, means: String, ty: Ty) = Symbol(SymbolName(n), means, SymbolType.Typed(ty))
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

  /** `authorized := (u: Term[UserId], p: Term[Path]) => grants.contains(Grant(u, p))` */
  private val grantTable =
    val (u, p) = (Binder(VarId(0), "u", userId), Binder(VarId(1), "p", path))
    val body = Expr.Prim(PrimOp.Contains, List(Expr.Sym(SymbolName("grants"), Ty.ListOf(grant)),
      Expr.Make(TypeName("Grant"), CtorName("Grant"), List(Expr.Var(u), Expr.Var(p)))), Ty.Bool)
    val fixing = Fixing.TermAs(SymbolName("authorized"), Written(Lambda(List(u, p), body, Ty.Bool), SourceText("…")))
    Node(NodeId("GrantTable"), Prose("A user is authorized for a path when a grant names them.", "…"),
      Statement.Definition(NonEmptyList.one(fixing)))

  /** A claim over `access`, whose type names both opaque types. */
  private val accessExactly =
    val (u, r) = (Binder(VarId(2), "u", user), Binder(VarId(3), "r", resource))
    val call = Expr.Apply(Expr.Sym(SymbolName("access"), Ty.FnOf(List(user, resource), Ty.Bool)),
      List(Expr.Var(u), Expr.Var(r)), Ty.Bool)
    Node(NodeId("AccessExactly"), Prose("…", "…"),
      Statement.Claim(Written(Expr.Quant(frflow.core.expr.Quantifier.Forall, List(u, r), call), SourceText("…")), Nil))

  private val theory = Theory(KbName("Auth"), vocabulary,
    List(grantTable, accessExactly).map(Sited(_, Span(RelPath.fromIdentifiers("src", "Auth.scala"), 0))), Nil,
    CodeTable(Map.empty, Map.empty))

  test("a definition's vocabulary is the term it defines and what its body mentions (GrantTable)") {
    assertEquals(Texts.vocabulary(theory, NodeId("GrantTable")),
      List(s"authorized: $authorizedMeans", s"grants: $grantsMeans"))
  }

  test("a claim's vocabulary has the opaque types its terms are over (AccessExactly, in part)") {
    assertEquals(Texts.vocabulary(theory, NodeId("AccessExactly")),
      List("Resource: something a user may want to access", "User: a person who uses the system",
        s"access: $accessMeans"))
  }

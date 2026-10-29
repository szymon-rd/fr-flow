package frflow.project

import frflow.core.name.NodeId
import frflow.dsl.kb.FrModel
import frflow.proof.layout.{Layout, NodePart}
import frflow.proof.audit.Completeness
import frflow.proof.lean.ast.{Decl, LeanModule}

/** Every rule of `always` the ported examples' Lean takes as a hypothesis is discharged, and every node is asked
  * what its place asks, as an oracle reads it apart from the obligations' own selection (`Completeness`): each
  * store's start and each program changing it, each maker of its type, each hand-off of one to code not proven, at
  * its call; each `complete`, `impl` and `commute_<i>`. And the oracle sees an obligation gone, which the laying out
  * itself refuses as a FrFlow bug.
  */
class CompletenessSuite extends munit.FunSuite:
  private val examples: List[(String, FrModel)] = List("rooms" -> _root_.rooms.rooms, "auth" -> _root_.auth.knowledge,
    "crm" -> _root_.crm.knowledge, "keycloak" -> _root_.keycloak.knowledge)
  private lazy val analyses = examples.map((name, kb) => name -> Projects.bare(Projects.elaborated(kb)))

  /** The modules with the obligation `name` gone from the node's `Spec`. */
  private def without(modules: List[LeanModule], layout: Layout, node: NodeId, name: String) = modules.map(m =>
    if m.name != layout.ofNode(node, NodePart.Spec) then m
    else m.copy(decls = m.decls.map {
      case Decl.Namespace(n, ds) => Decl.Namespace(n, ds.filterNot {
          case Decl.Documented(_, Decl.Def(_, x, _, _, _)) => x.text == name
          case _                                           => false
        })
      case other                 => other
    }))

  examples.foreach { (name, _) =>
    test(s"$name: every rule a statement assumes has its start, its cover_ and its made_ stated") {
      val a = analyses.toMap.apply(name)
      assertEquals(Completeness.of(a.decided, a.modules), Nil)
    }
  }

  test("an obligation gone from rooms' Lean is missed: a cover_, a made_ of a maker, the made_ at one call") {
    val a = analyses.head._2
    List("neverOverlap" -> "cover_book", "bookingsOfTheRoom" -> "made_inRoom",
      "bookingsOfTheRoom" -> "made_bookIfGranted_call_1", "bookingsOfTheRoom" -> "made_bookIfGranted_call_3")
      .foreach { (rule, obligation) =>
        val gone = without(a.modules, Layout(a.decided.theory.name), NodeId(rule), obligation)
        assertEquals(Completeness.of(a.decided, gone).map(m => (m.node.value, m.obligation)), List(rule -> obligation))
      }
  }

  test("a term built into an obligation ill-formed, or an obligation gone, is a FrFlow bug: no Lean is laid out") {
    import frflow.core.expr.Expr
    import frflow.core.name.{SourceText, SymbolName}
    import frflow.core.typing.IrError
    import frflow.proof.audit.{Audit, WellFormed}
    import frflow.proof.obligation.{Discharge, Obligation, ObligationName, Prop}
    val a = analyses.head._2
    val built = a.obligations.flatMap(o => o.required ++ o.tried) ++ a.whole
    assertEquals(WellFormed.of(a.decided, built), Nil)
    val big = frflow.core.ty.Ty.Num(frflow.core.ty.NumKind.Big)
    val misread = frflow.core.spec.Written.formula([T[_]] => (s: frflow.core.term.Sym[T]) =>
      s.eq(s.param[BigInt](SymbolName("inRoom"), big), s.param[BigInt](SymbolName("inRoom"), big)), SourceText("…"))
    val ill = Obligation(ObligationName.Made("inRoom"), Prop.Formula(misread, Map.empty), Discharge.Auto, "…")
    assertEquals(WellFormed.of(a.decided, List(ill)), List.fill(2)(ill.name ->
      IrError.Mistyped(Expr.Sym(SymbolName("inRoom"), big))))
    val gone = without(a.modules, Layout(a.decided.theory.name), NodeId("neverOverlap"), "cover_book")
    List(() => Audit.checked(a.decided, ill :: built, a.modules), () => Audit.checked(a.decided, built, gone))
      .map(laid => intercept[IllegalStateException](laid())).foreach(e => assert(e.getMessage.startsWith("FrFlow bug")))
    assertEquals(Audit.checked(a.decided, built, a.modules), a.modules)
  }

  test("every complete, impl and commute_ the ports and the parallel programs state, gone, is missed: of its node") {
    val asked = "complete|impl|commute_[0-9]+".r
    val programs = frflow.proof.layout.Programs.resolved
    val all = analyses.map(_._2).map(a => a.decided -> a.modules) :+
      (programs -> frflow.proof.layout.Laid(programs, Map.empty, Nil).modules)
    val seen = all.flatMap { (r, modules) =>
      val layout = Layout(r.theory.name)
      r.theory.refinement.nodes.flatMap(n => modules.filter(_.name == layout.ofNode(n.id, NodePart.Spec))
        .flatMap(_.decls).collect { case Decl.Namespace(_, ds) => ds }.flatten.collect {
          case Decl.Documented(_, Decl.Def(_, x, _, _, _)) if asked.matches(x.text) => n.id -> x.text
        }).map { (id, obligation) =>
        val gone = without(modules, layout, id, obligation)
        assertEquals(Completeness.of(r, gone).map(m => (m.node, m.obligation)), List(id -> obligation))
        obligation.takeWhile(_ != '_')
      }
    }
    assertEquals(seen.distinct.sorted, List("commute", "complete", "impl"))
  }

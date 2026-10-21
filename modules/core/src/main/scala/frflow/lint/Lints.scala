package frflow.lint

import frflow.dsl.LayerKind
import frflow.ir.*
import frflow.model.*
import frflow.render.Nodes

enum Severity:
  case Error, Warning

final case class LintIssue(severity: Severity, nodeId: Option[String], code: String, message: String):
  def render: String =
    val where = nodeId.fold("")(id => s"[$id] ")
    s"${severity.toString.toLowerCase} $code: $where$message"

/** Structural and coherence rules of a layered model. Errors block rendering,
  * checking and approval; warnings are reported.
  */
object Lints:

  final case class Limits(
      maxStatementChars: Int = 400,
      maxStatementSentences: Int = 3,
      maxChildren: Int = 7
  )

  /** Names the renderer generates inside a layer namespace. */
  val ReservedNames: Set[String] =
    Set("State", "Init", "machine", "abs", "glue", "Obl", "Proofs", "Auto", "Hyp", "invariant", "refinement", "Laws",
      Nodes.TheoryId)

  private val Ident = """[A-Za-z_][A-Za-z0-9_]*""".r

  /** Names used unescaped in generated Lean: identifiers that are not Lean keywords. */
  def isValidIdent(s: String): Boolean = Ident.matches(s) && !frflow.render.LeanPrinter.isKeyword(s)

  def run(m: TheoryModel, limits: Limits = Limits()): Seq[LintIssue] =
    val issues = Seq.newBuilder[LintIssue]
    def err(node: Option[String], code: String, msg: String) = issues += LintIssue(Severity.Error, node, code, msg)
    def warn(node: Option[String], code: String, msg: String) = issues += LintIssue(Severity.Warning, node, code, msg)
    val theory = Some(Nodes.TheoryId)

    // -- theory -------------------------------------------------------------------
    if !isValidIdent(m.name) then err(None, "FR001", s"theory name '${m.name}' is not a valid identifier")
    if m.layers.isEmpty then err(None, "FR002", "model has no layers")
    m.roots match
      case List(r) if r.kind != LayerKind.Requirements => err(Some(r.id), "FR003", "the root layer must be a Requirements layer")
      case List(_) | Nil                              => ()
      case rs => err(None, "FR003", s"model must have exactly one root, found ${rs.map(_.id).mkString(", ")}")

    duplicates(m.layers.map(_.id)).foreach(d => err(None, "FR004", s"duplicate layer id '$d'"))
    duplicates(m.assumptions.map(_.id)).foreach(d => err(None, "FR006", s"duplicate assumption id '$d'"))
    duplicates(m.laws.map(_.name)).foreach(d => err(theory, "FR007", s"duplicate law '$d'"))

    val used = m.layers.flatMap(_.assumptionsUsed).toSet
    m.assumptions.foreach { a =>
      if a.statement.trim.isEmpty then err(theory, "FR009", s"assumption ${a.id} has no statement")
      if a.justification.trim.isEmpty then
        err(theory, "FR010", s"assumption ${a.id} has no justification (why the environment satisfies it)")
      if !used(a.id) then warn(theory, "FR011", s"assumption ${a.id} is not cited by any layer")
    }

    m.laws.foreach { l =>
      if !isValidIdent(l.name) || ReservedNames(l.name) then err(theory, "FR012", s"law name '${l.name}' is not a valid name")
      if l.lifted.result != Type.Bool then err(theory, "FR013", s"law ${l.name} must be a Boolean expression or a predicate")
      if l.statement.trim.isEmpty then err(theory, "FR014", s"law ${l.name} has no statement")
    }

    val layerIds = m.layers.map(_.id).toSet
    m.defs.adts.values.foreach { a =>
      val last = a.name.split('.').last
      if ReservedNames(last) || layerIds(a.name) then
        err(theory, "FR015", s"type ${a.scalaName} is translated to the reserved Lean name ${a.name}; rename it")
      if a.doc.isEmpty && m.theoryDefs.contains(a.name) then warn(theory, "FR016", s"domain type ${a.name} has no Scaladoc")
    }
    m.defs.funs.values.foreach { f =>
      if layerIds(f.name.split('.').head) then
        err(theory, "FR015", s"${f.scalaName} is translated to ${f.name}, which clashes with a layer namespace; rename it")
    }
    if m.domain.isEmpty then warn(theory, "FR017", "the theory declares no domain types (use `domain[...]`)")

    // -- layers ---------------------------------------------------------------------
    m.layers.foreach { l =>
      val id = Some(l.id)
      if !isValidIdent(l.id) || ReservedNames(l.id) then err(id, "FR020", s"layer id '${l.id}' is not a valid name")

      val stmt = l.statement.trim
      if stmt.isEmpty then err(id, "FR021", "statement is empty")
      if stmt.length > limits.maxStatementChars then
        err(id, "FR022", s"statement has ${stmt.length} characters (limit ${limits.maxStatementChars}); split the layer")
      val sentences = stmt.split("""(?<=[.!?])\s+""").count(_.trim.nonEmpty)
      if sentences > limits.maxStatementSentences then
        err(id, "FR023", s"statement has $sentences sentences (limit ${limits.maxStatementSentences})")
      if l.rationale.trim.isEmpty then warn(id, "FR024", "rationale is empty: record why this design step was chosen")

      val kids = m.children(l.id)
      if kids.size > limits.maxChildren then
        err(id, "FR025", s"layer has ${kids.size} children (limit ${limits.maxChildren}); introduce an intermediate layer")
      if l.kind == LayerKind.Implementation && kids.nonEmpty then
        err(id, "FR026", s"an implementation is the last refinement; ${kids.map(_.id).mkString(", ")} cannot refine it")
      if l.kind != LayerKind.Requirements && l.link.isEmpty then
        err(id, "FR027", "a refining layer must declare its abstraction to the parent layer")

      val isProduct = l.stateType match
        case Type.Named(n) => m.defs.adts.get(n).exists(_.shape.isInstanceOf[AdtShape.Product])
        case _             => false
      if !isProduct then err(id, "FR028", s"the state of a layer must be a case class, found ${l.stateType}")

      val names = l.ops.map(_.name) ++ l.invariants.map(_.name)
      duplicates(names).foreach(x => err(id, "FR030", s"name '$x' is declared more than once"))
      names.foreach { x =>
        if !isValidIdent(x) then err(id, "FR031", s"'$x' is not a valid identifier")
        if ReservedNames(x) then err(id, "FR032", s"'$x' is reserved by the renderer")
      }
      if l.ops.isEmpty then warn(id, "FR033", "layer has no operations")
      if l.kind == LayerKind.Requirements && !l.invariants.exists(_.requirement) then
        warn(id, "FR034", "the requirements layer states no requirement")
      if l.init.isEmpty then
        if l.kind == LayerKind.Implementation then err(id, "FR035", "the implementation must declare its initial state")
        else warn(id, "FR035", "no initial condition: every state is initial")
      l.cites.filterNot(c => m.assumption(c).isDefined).foreach { c =>
        err(id, "FR036", s"cites assumption $c, which the theory does not declare")
      }

      // Executability of the implementation
      if l.kind == LayerKind.Implementation then
        if !l.stateType.isData || stateHasFunctions(m, l.stateType) then
          err(id, "FR040", "the implementation state must be data: no function-valued fields")
        l.ops.foreach { op =>
          if !op.paramType.isData || stateHasFunctions(m, op.paramType) then
            err(id, "FR041", s"operation ${op.name}: parameters must be data")
          val executed = op.checks ++ op.act.toList
          if executed.exists(c => usesQuantifier(m, c.body)) then
            err(id, "FR042", s"operation ${op.name}: checks and effects must be executable (no forall/exists over types)")
        }
        l.init.foreach(i => if usesQuantifier(m, i.lifted.body) then err(id, "FR042", "the initial state must be executable"))

      val parent = m.parentOf(l)
      l.ops.foreach { op =>
        op.assumes.filterNot(a => m.assumption(a.assumption).isDefined).foreach { a =>
          err(id, "FR043", s"operation ${op.name}: assume clause cites undeclared assumption ${a.assumption}")
        }
        (parent, op.target) match
          case (None, TargetModel.Unspecified) => ()
          case (None, _) => err(id, "FR044", s"operation ${op.name}: operations of the root layer refine nothing")
          case (Some(_), TargetModel.Unspecified) =>
            err(id, "FR045", s"operation ${op.name}: every operation of a refining layer must refine a parent operation or skip")
          case (Some(p), TargetModel.Refines(layer, ao, _)) =>
            if layer != p.id then
              err(id, "FR046", s"operation ${op.name}: refines $layer.$ao, but only operations of the parent ${p.id} can be refined")
            else if p.op(ao).isEmpty then err(id, "FR046", s"operation ${op.name}: refines unknown operation ${p.id}.$ao")
          case (Some(_), TargetModel.Skip) => ()
      }

      // Parent operations that nothing refines can never happen in the refined system.
      parent.foreach { p =>
        val refined = l.ops.collect { case OpModel(_, _, _, _, _, _, TargetModel.Refines(_, ao, _)) => ao }.toSet
        p.ops.map(_.name).filterNot(refined).foreach { ao =>
          warn(id, "FR047", s"parent operation ${p.id}.$ao is not refined by any operation (it becomes disabled)")
        }
      }
    }
    issues.result()

  private def usesQuantifier(m: TheoryModel, e: Expr): Boolean =
    def go(e: Expr, seen: Set[String]): Boolean =
      e.hasQuantifier || e.calls.exists(n => !seen(n) && m.defs.funs.get(n).exists(f => go(f.body, seen + n)))
    go(e, Set.empty)

  private def stateHasFunctions(m: TheoryModel, t: Type): Boolean =
    def go(t: Type, seen: Set[String]): Boolean = t match
      case Type.Fun(_, _)   => true
      case Type.Named(n) if !seen(n) =>
        m.defs.adts.get(n).exists { a =>
          val fieldTypes = a.shape match
            case AdtShape.Product(fs) => fs.map(_.tpe)
            case AdtShape.Sum(cs)     => cs.flatMap(_.fields.map(_.tpe))
          fieldTypes.exists(go(_, seen + n))
        }
      case Type.ListOf(e)   => go(e, seen)
      case Type.SetOf(e)    => go(e, seen)
      case Type.MapOf(k, v) => go(k, seen) || go(v, seen)
      case Type.OptionOf(e) => go(e, seen)
      case Type.TupleOf(es) => es.exists(go(_, seen))
      case _                => false
    go(t, Set.empty)

  def errors(issues: Seq[LintIssue]): Seq[LintIssue] = issues.filter(_.severity == Severity.Error)

  private def duplicates(xs: Seq[String]): Seq[String] =
    xs.groupBy(identity).collect { case (k, v) if v.size > 1 => k }.toSeq.sorted

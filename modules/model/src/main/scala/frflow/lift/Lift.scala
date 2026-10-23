package frflow.lift

import frflow.*
import scala.collection.mutable
import scala.quoted.*

/** Compile-time translation of Scala lambdas over domain ADTs to Lean terms.
  *
  * Supported: case classes (structures) and Scala 3 enums (inductive types);
  * `Boolean` (as `Prop`), `Int`/`Long` (as `Int`), `String`, `List`, `Option`,
  * tuples; constructors, field access, `copy`, `match`, `if`, `val`s;
  * `==`, `!=`, `&&`, `||`, `!`, `==>`, integer arithmetic and comparison; a few
  * `List`/`Option`/`Map`/`Set` operations (`xs.toSet`: a list's membership); `forall`/`exists`; calls to `define`d functions;
  * opaque types (`User.T`) and parameters (`authorized(u, r)`, `shares.value`).
  * Anything else is a compile error at its position.
  *
  * The entry points of the inline methods are here; `Translator` translates a lambda (its types in
  * `TypeTranslation`). Each macro expansion collects what it finds in mutable buffers of one
  * translator, which lives for that expansion only.
  */
private[frflow] object Lift:

  def lifted[F: Type](f: Expr[F])(using Quotes): Expr[Lifted[F]] = Translator().lift(f)

  def define[F: Type](f: Expr[F])(using Quotes): Expr[Def[F]] =
    val t = Translator()
    val name = t.defName
    val l = t.lift(f)
    '{ new Def[F](${ Expr(name) }, $l) }

  def leanType[T: Type](using Quotes): Expr[LeanType] = Translator().leanType[T]

  /** A lambda kept as Scala only (a node out of Lean), with its source text and the definitions,
    * parameters and opaque types it refers to: a change to them still reaches the node.
    */
  def informal[F: Type](f: Expr[F])(using Quotes): Expr[Lifted[F]] =
    import quotes.reflect.*
    val term = unwrap(f.asTerm)
    val found = scala.collection.mutable.LinkedHashMap.empty[String, (String, Term)]
    def kind(t: TypeRepr): Option[String] =
      val n = t.widen.dealias.typeSymbol.fullName
      Option.when(Set("frflow.Param", "frflow.Def", "frflow.Opaque")(n))(n)
    object refs extends TreeTraverser:
      override def traverseTree(t: Tree)(owner: Symbol): Unit =
        t match
          case r: Ident if r.symbol.isValDef || (r.symbol.isTerm && r.symbol.flags.is(Flags.Module)) =>
            kind(r.tpe).foreach(k => found.getOrElseUpdate(r.symbol.fullName, (k, r)))
          case r: Select if r.symbol.isValDef =>
            kind(r.tpe).foreach(k => found.getOrElseUpdate(r.symbol.fullName, (k, r)))
          case tt: TypeTree =>
            // `User.T`: the opaque type a lambda's binder is declared with
            def opaques(tp: TypeRepr): Unit = tp match
              case TypeRef(prefix: TermRef, _) if kind(prefix).contains("frflow.Opaque") =>
                found.getOrElseUpdate(prefix.termSymbol.fullName, ("frflow.Opaque", Ref(prefix.termSymbol)))
              case AppliedType(c, args) => opaques(c); args.foreach(opaques)
              case _ => ()
            opaques(tt.tpe)
          case _ => ()
        super.traverseTree(t)(owner)
    refs.traverseTree(term)(Symbol.spliceOwner)
    def of[T: Type](k: String): Expr[List[T]] = Expr.ofList(found.values.collect { case (`k`, r) => r.asExprOf[T] }.toList)
    // A formula (`() => formula`, built by `Node.claim`) reads as the caller's expression.
    val shown = term match
      case Lambda(Nil, b) => unwrap(b)
      case t              => t
    val text = shown.pos.sourceCode.getOrElse(shown.show)
    val defs = of[Def[?]]("frflow.Def")
    val params = of[Param[?]]("frflow.Param")
    val opaques = of[Opaque]("frflow.Opaque")
    '{ def liftedNode(): Lifted[F] = new Lifted[F](() => $f, Nil, "", "", ${ Expr(text) }, Nil, Nil, Nil, () => $defs, () => $params, () => $opaques); liftedNode() }

  /** The source files of the project code an expression refers to (an implementation's classes).
    * FrFlow's own code (package `frflow`, wherever its sources are) is not the project's.
    */
  def sourceFiles(e: Expr[Any])(using Quotes): Expr[List[String]] =
    import quotes.reflect.*
    val files = mutable.LinkedHashSet.empty[String]
    def library(s: Symbol): Boolean = s.fullName == "frflow" || s.fullName.startsWith("frflow.")
    def add(s: Symbol): Unit =
      if !s.isNoSymbol && !library(s) then
        s.pos.map(p => java.nio.file.Paths.get(p.sourceFile.path)).filter(java.nio.file.Files.isRegularFile(_))
          .map(_.toAbsolutePath.normalize.toString).filter(_.endsWith(".scala")).foreach(files += _)
    object T extends TreeTraverser:
      override def traverseTree(t: Tree)(owner: Symbol): Unit =
        t match
          case r: Ref => add(r.symbol); add(r.symbol.owner)
          case n: New => add(n.tpe.typeSymbol)
          case _      => ()
        super.traverseTree(t)(owner)
    T.traverseTree(e.asTerm)(Symbol.spliceOwner)
    add(e.asTerm.tpe.widen.typeSymbol)
    val own = Some(java.nio.file.Paths.get(Position.ofMacroExpansion.sourceFile.path).toAbsolutePath.normalize.toString)
    // Relative to the build's directory, so the paths hold in any checkout.
    val base = java.nio.file.Paths.get("").toAbsolutePath.normalize
    val kept = files.toList.filterNot(f => own.contains(f) && files.size > 1)
    def rel(f: String) = { val p = java.nio.file.Paths.get(f); if p.startsWith(base) then base.relativize(p).toString else f }
    // The model's own file comes last: it is where the implementation is attached, not part of it.
    Expr(kept.map(rel) ++ own.filter(o => !kept.contains(o)).map(rel))

  /** The source file of the call site, relative to the build's directory: where a node is defined. */
  def here(using Quotes): Expr[String] =
    import quotes.reflect.*
    val base = java.nio.file.Paths.get("").toAbsolutePath.normalize
    val p = java.nio.file.Paths.get(Position.ofMacroExpansion.sourceFile.path).toAbsolutePath.normalize
    Expr(if p.startsWith(base) then base.relativize(p).toString else p.toString)

  def at(using Quotes): Expr[Int] =
    import quotes.reflect.*
    Expr(Position.ofMacroExpansion.start)

  def sources(xs: Expr[Seq[Any]])(using Quotes): Expr[List[String]] =
    import quotes.reflect.*
    // Through inline calls the argument arrives wrapped; its own position is the caller's text.
    def text(e: Expr[Any]) = unwrap(e.asTerm).pos.sourceCode.getOrElse(e.show)
    xs match
      case Varargs(es) => Expr(es.map(text).toList)
      case other       => Expr(List(text(other)))

  /** A term without the wrapping inline calls, ascriptions and empty blocks put around it. */
  private def unwrap(using q: Quotes)(t: q.reflect.Term): q.reflect.Term =
    import q.reflect.*
    t match
      case Inlined(_, _, b) => unwrap(b)
      case Typed(b, _)      => unwrap(b)
      case Block(Nil, b)    => unwrap(b)
      case _                => t

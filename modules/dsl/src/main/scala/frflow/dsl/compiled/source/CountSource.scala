package frflow.dsl.compiled.source

import frflow.dsl.compiled.Inspect
import scala.collection.mutable
import scala.quoted.Quotes

/** How many trees of each form the TASTy of a place holds, counted by the compiler's own traversal
  * (`TreeTraverser`), which the reading (`ReadSource`) does not use: so that the two can be compared, and a tree
  * the reading passed over, or read twice, would show. Types are not counted: the reading takes a type tree as
  * the type it denotes.
  */
object CountSource:
  def apply(cls: Class[?]): Map[String, Int] = Inspect.files(cls)(q => files => Counter[q.type](q).of(files.map(_._2)))

  private final class Counter[Q <: Quotes & Singleton](val q: Q):
    import q.reflect.*
    private val seen = mutable.Map.empty[String, Int].withDefaultValue(0)

    def of(roots: List[Tree]): Map[String, Int] =
      roots.foreach(r => walk.traverseTree(r)(Symbol.spliceOwner))
      seen.toMap

    /** A type is counted where the reading keeps it as a tree (`TypeTree`): a parent of a class, and the call
      * of an inlining that names only the class it was written in. No other type is, nor what is inside one. A
      * file's package is its name, not a tree. An inlined call's own tree is walked too, which the compiler's
      * traversal leaves out.
      */
    private val walk: TreeTraverser = new TreeTraverser:
      override def traverseTree(t: Tree)(owner: Symbol): Unit = t match
        case _: TypeTree | _: TypeBoundsTree => ()
        case PackageClause(_, stats)         =>
          seen("PackageClause") += 1
          stats.foreach(traverseTree(_)(owner))
        case ClassDef(_, _, parents, _, _)   =>
          seen("TypeTree") += parents.count(isType)
          count(t, owner)
        case Inlined(call, _, _)             =>
          seen("TypeTree") += call.count(isType)
          call.foreach(traverseTree(_)(owner))
          count(t, owner)
        case _                               => count(t, owner)

      private def count(t: Tree, owner: Symbol): Unit =
        seen(form(t)) += 1
        traverseTreeChildren(t)(owner)

    private def isType(t: Tree): Boolean = t match
      case _: TypeTree => true
      case _           => false

    private def form(t: Tree): String = t match
      case PackageClause(_, _) => "PackageClause"
      case _: ClassDef         => "ClassDef"
      case _: TypeDef          => "TypeDef"
      case _: DefDef           => "DefDef"
      case _: ValDef           => "ValDef"
      case Wildcard()          => "Wildcard"
      case _: Typed            => "Typed"
      case e: Term             => term(e)
      case other               => clause(other)

    /** A term's form is the name of the compiler's class for it, but where the reader the compiler gives names
      * it otherwise: a quote or a splice of a macro is the call it stands for.
      */
    private def term(t: Term): String = t match
      case SummonFrom(_)  => "SummonFrom"
      case Match(_, _)    => "Match"
      case Repeated(_, _) => "Repeated"
      case other          => other.getClass.getSimpleName match
        case "InlineMatch"      => "Match"
        case "WhileDo"          => "While"
        case "SeqLiteral"       => "Repeated"
        case "Quote" | "Splice" => "Apply"
        case name               => name

    private def clause(t: Tree): String = t match
      case _: Import            => "Imported"
      case _: Export            => "Exported"
      case CaseDef(_, _, _)     => "CaseDef"
      case Bind(_, _)           => "Bind"
      case Unapply(_, _, _)     => "Unapply"
      case Alternatives(_)      => "Alternatives"
      case TypedOrTest(_, _)    => "TypeTest"
      case other                => other.getClass.getSimpleName

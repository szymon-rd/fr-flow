package frflow.core.threads

import scala.annotation.tailrec

/** A unit of code read (`Draft`), laid out as a file (`Program`).
  *
  *   - A group's definitions keep the order of the source, but each comes after those of the group it calls: the
  *     group is passed over in order, as many times as it takes, each pass writing the definitions whose callees
  *     are written.
  *   - Each closure is named and what it runs written after the definition that makes it (`Closures`).
  *   - Of what the definitions may mention (`Support`), the file holds what they do: the globals in the order they
  *     are first mentioned; the casts likewise, one that calls another directly after it; the methods of a class
  *     not read in the order it declares them; and `obj`, the cases shared with the caller, then the others in
  *     the order they are first mentioned.
  */
object Assemble:
  def apply(draft: Draft): Program =
    val laid = groups(draft.groups)
    val used = closed(laid.sections.flatMap(_.defs).flatMap(Decl.mentions).distinct, draft.support.casts)
    val support = draft.support
    val held = used.flatMap(n => support.held.find(_.name == n)).filterNot(support.shared.contains)
    val obj = Decl.Inductive("obj", support.shared ++ held)
    val externs = support.externs.map(s => s.copy(defs = s.defs.filter(d => used.contains(d.name))))
    Program(draft.types :+ obj, laid.closures, used.flatMap(n => support.globals.find(_.name == n)) ++
      casts(support.casts, used), externs.filter(_.defs.nonEmpty), laid.sections, draft.holds)

  /** The sections written so far, the closures made, and how many of each method's. */
  private final case class Laid(counts: Map[String, Int], sections: List[Section], closures: List[Ctor])

  private def groups(all: List[Draft.Group]): Laid =
    all.foldLeft(Laid(Map.empty, Nil, Nil)) { (so, group) =>
      val (after, defs) = ordered(group.defs, Nil).foldLeft((so, List.empty[Decl.Definition]))(place)
      after.copy(sections = after.sections :+ Section(group.title, defs)) }

  /** A definition written, with what its closures run after it. */
  private def place(at: (Laid, List[Decl.Definition]), read: Draft.Read): (Laid, List[Decl.Definition]) =
    val (so, defs) = at
    val from = so.counts.getOrElse(read.base, 0)
    val (definition, lifted) = Closures.lift(read, from)
    (so.copy(counts = so.counts.updated(read.base, from + lifted.size), closures = so.closures ++
      lifted.map(_.ctor)), defs ++ (definition :: lifted.map(_.body)))

  /** `left` after `done`, in passes: a pass writes, in order, each definition that calls none still left. */
  @tailrec private def ordered(left: List[Draft.Read], done: List[Draft.Read]): List[Draft.Read] =
    val (written, waiting) = left.foldLeft((done, List.empty[Draft.Read])) { case ((placed, kept), read) =>
      val unwritten = left.map(_.definition.name).toSet -- placed.map(_.definition.name) - read.definition.name
      if Decl.mentions(read.definition).exists(unwritten) then (placed, kept :+ read) else (placed :+ read, kept) }
    if waiting.isEmpty || waiting.size == left.size then written ++ waiting else ordered(waiting, written)

  /** `names`, and the names the casts among them mention, and so on, in the order of first mention. */
  @tailrec private def closed(names: List[String], casts: List[Decl.Definition]): List[String] =
    val more = (names ++ casts.filter(c => names.contains(c.name)).flatMap(Decl.mentions)).distinct
    if more.size == names.size then names else closed(more, casts)

  /** The casts mentioned, in the order of first mention, one that calls another directly after it. */
  private def casts(all: List[Decl.Definition], used: List[String]): List[Decl.Definition] =
    val taken = used.flatMap(n => all.find(_.name == n))
    def calls(c: Decl.Definition, d: Decl.Definition): Boolean =
      c.name != d.name && Decl.mentions(c).contains(d.name)
    val (after, first) = taken.partition(c => taken.exists(calls(c, _)))
    first.flatMap(d => d :: after.filter(calls(_, d)))

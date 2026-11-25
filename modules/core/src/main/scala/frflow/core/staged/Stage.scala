package frflow.core.staged

import frflow.core.code.Datum
import frflow.core.effect.Idents
import scala.collection.mutable

/** Stage 1 for code given a meaning by its tree (`docs/EFFECT-TREES.md`): the files read, staged into one
  * program per method, per initialiser of a class, per function made in the code and per argument taken
  * unevaluated. A program is the operations `FrFlow/Scala/Meaning.v` gives the tree, in order, with what that
  * meaning reads of the tree and of the scope read here. A unit the staging does not take is left out, with
  * the reason: the meaning of its tree then answers for it.
  */
object Stage:
  def apply(files: List[Datum]): StagedCode =
    val stager = Stager(Defined(files.map(Tree.of)))
    stager.all()
    StagedCode(stager.staged.toList, stager.unstaged.toList, stager.called.toList)

  private final class Stager(val table: Defined) extends StagePatterns:
    import Tree.*
    val staged: mutable.ListBuffer[StagedUnit] = mutable.ListBuffer.empty
    val unstaged: mutable.ListBuffer[(String, String)] = mutable.ListBuffer.empty

    def all(): Unit = table.everyClass.foreach { c =>
      within = c.name
      unit(s"init ${c.name}")(initialiser(c))
      c.body.foreach {
        case d @ DefDef(s: Sym.Member, _, _, Some(body), _) => unit(s.key)(method(c, d, body))
        case _                                              => ()
      }
    }

    /** One unit and those made inside it, kept together or left out together. */
    private def unit(what: String)(make: => StagedUnit): Unit =
      nested.clear()
      try
        val made = make
        staged += made
        staged ++= nested
      catch case e: Unstaged => unstaged += (what -> e.why)

    /** The scope a member's body is read in: `this`, of each class the object is of. */
    private def ofThis(c: ClassDef, names: Names): Env =
      Env(table.own(c.name).map(a => s"this:$a" -> Bound.Plain(V.Var("this"))).toMap, Some("sc"), names)

    private def named(owner: String, name: String): String =
      s"${Idents.plain(owner.split('.').last)}_${Idents.plain(name)}_${numbered()}"

    private def method(c: ClassDef, d: DefDef, body: Tree): StagedUnit =
      val names = Names()
      val params = Defined.params(d).map(p => (p, names.fresh(p.s.key.takeWhile(_ != '#'))))
      val program = expr(body)(using ofThis(c, names).havingAll(params.map(given_)))
      StagedUnit(UnitKind.Method(d.s), "m_" + named(c.name, d.s.key.split('.').last),
        P.Bind("sc", op("captured", variable("this")), P.Given(params.map(_._2), program)))

    /** What making an object of a class runs on it (`Meaning.init`). */
    private def initialiser(c: ClassDef): StagedUnit =
      val names = Names()
      val ps = c.ctor match
        case d: DefDef => Defined.params(d).map(p => (p, names.fresh(p.s.key.takeWhile(_ != '#'))))
        case _         => Nil
      given Env = ofThis(c, names).havingAll(ps.map(given_))
      val program = accessors(c, ps)(parents(c)(members(c.body)(P.Give(V.Unit))))
      StagedUnit(UnitKind.Init(c.name), "init_" + named(c.name, "new"),
        P.Bind("sc", op("captured", variable("this")), P.Given(ps.map(_._2), program)))

    private def written(name: String, v: V): P = op("set_field", variable("this"), Arg.Text(name), value(v))

    /** The constructor's parameters that are fields, written. */
    private def accessors(c: ClassDef, ps: List[(ValDef, String)])(next: P): P =
      val given_ = ps.map((p, x) => name(p.s) -> x).toMap
      c.body.foldRight(next) {
        case (ValDef(s, flags, _, None), rest) if flags.contains("ParamAccessor") =>
          given_.get(name(s)).fold(rest)(x => after(written(name(s), V.Var(x)))(rest))
        case (_, rest)                                                            => rest
      }

    private def name(s: Sym): String = s match
      case Sym.Member(_, n, _) => n
      case Sym.Local(n, _)     => n
      case Sym.NoSym           => ""

    /** Each parent that is a class of the code, initialised with what it is given. */
    private def parents(c: ClassDef)(next: P)(using Env): P = c.parents.foldRight(next) { (p, rest) =>
      Defined.made(p).flatMap(Defined.tyClass).filter(table.classOf(_).isDefined).fold(rest)(parent =>
        each(Defined.spineArgs(p).map(expr), "arg")(vs =>
          after(op("init_", Arg.Text(parent), variable("this"), Arg.Vals(vs)))(rest)))
    }

    /** The values and statements of a class's body, in order. */
    private def members(body: List[Tree])(next: P)(using Env): P = body.foldRight(next) {
      case (ValDef(s, flags, _, Some(rhs)), rest) =>
        if flags.contains("Lazy") || flags.contains("Module") then rest
        else bind(expr(rhs), name(s))(v => after(written(name(s), v))(rest))
      case (_: ValDef | _: DefDef | _: ClassDef | Unmeant("TypeDef" | "Imported" | "Exported"), rest) => rest
      case (other, rest)                          => after(expr(other))(rest)
    }

package frflow.dsl.compiled.threads

import frflow.core.threads.{Arm, Decl, Draft, Param, Pattern, Section, Support, Term as Rocq, Ty}
import frflow.dsl.compiled.threads.reading.{Res, Step}

/** The definitions of the unit, each read from its method.
  *
  *   - A method's body is read for its result, in a scope of its parameters and `this`: a field of a class is `C_f
  *     this`; a trait with parameters that is a case of a sum takes `this` apart (`let (fields) := this in`).
  *   - A class's constructor, `C_new`, runs the initialisers of its fields in order and gives the record. One of
  *     a class that extends a class with a constructor of its own is not read.
  *   - A sum's method calls the method of the case `this` is.
  *   - A definition whose body is not read is `chaos` named for its method.
  *   - A method of a class not read is `extern` named for it.
  */
private[threads] trait ReadClasses extends ReadClosures:
  import q.reflect.*

  private val This = "this"

  def draft: Draft =
    val groups = entries.map((title, all) => Draft.Group(title, all.map(define)))
    Draft(declared, groups, Support(shared, catalogue.held, catalogue.globals, catalogue.casts, externs),
      repr(Symbol.requiredClass(unit.holds).typeRef), catalogue.unread)

  private def define(entry: Entry): Draft.Read = Draft.Read(entry.sig.base, entry match
    case Entry.Method(sig)              => defined(sig)
    case Entry.Constructor(sig, record) => constructor(sig, record)
    case Entry.Dispatch(sig, sum)       => dispatch(sig, sum))

  private def empty: Env = Env(Map.empty, Map.empty, None, Map.empty, Nil)

  /** `this` in a method of the class read as `on`: a record's fields are read off it, a case's are its parts. */
  private def self(cls: Symbol, on: String): (List[Step], Self, Env) =
    val value = Res.value(Rocq.Ref(This), Ty.Named(on))
    val known = empty.local(This, Ty.Named(on))
    sums.flatMap(_.cases).find(_.sym == cls).flatMap(_.fields) match
      case Some(fields) =>
        val params = fields.map(_._2)
        (List(Step.Unpack(params.map(_.name), Rocq.Ref(This))), Self(cls, value,
          params.map(p => p.name -> Res.value(Rocq.Ref(p.name), p.ty)).toMap),
          params.foldLeft(known)((e, p) => e.local(p.name, p.ty)))
      case None         =>
        val fields = record(on).toList.flatMap(_.fields.map(_._2))
        (Nil, Self(cls, value, fields.map(p => p.name -> Res.value(Rocq.of(Decl.projection(on, p.name),
          Rocq.Ref(This)), p.ty)).toMap), known)

  private def defined(sig: Sig): Decl.Definition =
    val (steps, env) = sig.on.fold((List.empty[Step], empty)) { on =>
      val (steps, self, known) = this.self(sig.sym.owner, on)
      (steps, known.copy(self = Some(self))) }
    val body = orChaos(sig.sym)(sig.sym.tree match
      case DefDef(_, _, _, Some(rhs)) =>
        Step.before(steps, tail(rhs, Goal.As(sig.result))(using withParams(env, sig.sym)).term)
      case _                          => refuse(s"${sig.name}, which has no body"))(identity)
    Decl.Definition(sig.name, sig.on.map(on => Param(This, Ty.Named(on))).toList ++ sig.params, Decl.M(sig.result),
      body)

  private def constructor(sig: Sig, record: Record): Decl.Definition =
    val fields = record.fields.map(_._2)
    val params = record.fields.filter((_, p) => sig.params.exists(_.name == p.name))
    val env = params.foldLeft(withParams(empty, sig.sym))((e, f) => e.named(f._1, f._2.name, f._2.ty))
    val made = Rocq.ret(Rocq.of(Decl.maker(record.name), fields.map(p => Rocq.Ref(p.name))*))
    val body = orChaos(sig.sym)(initialising(record.sym) match
      case Nil     => Step.before(statements(initialised(record.sym), Literal(UnitConstant()))(using env)._1, made)
      case parents => refuse(s"${sig.name}: the constructor of ${parents.map(_.fullName).mkString(", ")} runs too")
    )(identity)
    Decl.Definition(sig.name, sig.params, Decl.M(sig.result), body)

  /** The method of a sum: the method of each case, called on what the case holds. */
  private def dispatch(sig: Sig, sum: Sum): Decl.Definition =
    val args = sig.params.map(p => Rocq.Ref(p.name))
    val arms = sum.cases.map { c =>
      val called = sigs.find(s => s.sym.owner == c.sym && s.sym.allOverriddenSymbols.contains(sig.sym))
        .getOrElse(refuse(s"${sig.name}: the case ${c.ctor} has no such method in the unit"))
      if c.sym.flags.is(Flags.Module) then Arm(Pattern.of(c.ctor), Rocq.of(called.name, args*))
      else Arm(Pattern.of(c.ctor, "x"), Rocq.of(called.name, (Rocq.Ref("x") :: args)*)) }
    Decl.Definition(sig.name, Param(This, Ty.Named(sum.name)) :: sig.params, Decl.M(sig.result),
      Rocq.Match(Rocq.Ref(This), arms))

  /** For each class not read, each of its methods as a definition that is `extern`; one whose types are not read
    * has none.
    */
  private def externs: List[Section] = unit.opaque.map { name =>
    val cls = Symbol.requiredClass(name)
    val methods = cls.declarations.filter(d => d.isDefDef && !d.isClassConstructor && !made(d))
    Section(s"$name: not read. Its methods are taken to touch nothing of the JDK's state here.",
      methods.flatMap(m => scala.util.Try(extern(m)).toOption)) }

  private def extern(m: Symbol): Decl.Definition =
    Decl.Definition(externName(m), Param(This, Ty.Nat) :: paramsOf(m), Decl.M(resultOf(m)),
      Rocq.of("extern", Rocq.Text(s"${m.owner.fullName}.${m.name}")))

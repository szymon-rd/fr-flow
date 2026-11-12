package frflow.dsl.compiled.steps

import frflow.core.name.DefName
import frflow.dsl.build.{AsWritten, Source, WrittenAt}
import frflow.dsl.lifted.{FrSpec, Lifting}
import frflow.dsl.lifted.steps.Among
import frflow.dsl.term.LeanType
import frflow.dsl.term.Term as DTerm
import frflow.dsl.vocab.Definition as Defined

/** One member of a class that implements a structure, as code (`ClassCode`): a function of the class's state and
  * the member's inputs, compiled from the method's body. A member that changes the structure gives its result
  * with the state after it; one that only asks gives its result. A member that changes the structure is also
  * compiled among other calls (`among`): each call it makes of a structure it holds is a step, before which the
  * others may have left the state as a schedule says; it gives its result and the state after with what each
  * step did.
  */
private[steps] final class Members(val steps: Steps, val state: FrSpec[Any]):
  import steps.c
  import c.q.reflect.*

  /** A member as the class has it: its inputs, its body, and the type of its result. */
  private final case class Member(cls: Symbol, member: Symbol, inputs: List[ValDef], body: Term, result: TypeRepr):
    def changes: Boolean = member.flags.is(Flags.Mutable)
    def env(self: DTerm[Any], given_ : List[DTerm[Any]]): c.Env =
      c.Env.of(((cls, self) :: inputs.map(_.symbol).zip(given_))*)
    /** The state as the code's first input: named as the structure. */
    def named: String = steps.decapitalized(c.structureOf(cls.typeRef).fold(cls.name)(_.name))
    def gives: FrSpec[Any] = c.spec(result, body)
    def params: List[(String, FrSpec[Any])] = inputs.map(i => (i.name, c.spec(i.tpt.tpe, i)))

  /** The code a member is given: what its name ends with, its inputs (the state the first), what it gives. */
  private final case class Shape(suffix: String, params: List[(String, FrSpec[Any])], out: FrSpec[Any])

  private def memberOf(cls: Symbol, member: Symbol, result: TypeRepr): Member =
    val method = cls.declaredMethod(member.name).headOption.flatMap(c.kept)
    Member(cls, member, method.fold(Nil)(_.termParamss.flatMap(_.params)),
      method.map(_.rhs.get).getOrElse(field(cls, member)), result)

  def of(cls: Symbol, member: Symbol, result: TypeRepr): Defined[?] =
    val m = memberOf(cls, member, result)
    val out = if m.changes then steps.pair(m.gives, state).asInstanceOf[FrSpec[Any]] else m.gives
    lifted(m, Shape("", (m.named, state) :: m.params, out))(xs => alone(m, xs.head, xs.tail, out))

  /** The member among other calls, where it changes the structure and has at most two inputs. */
  def among(cls: Symbol, member: Symbol, result: TypeRepr): Option[Defined[?]] =
    val m = memberOf(cls, member, result)
    Option.when(m.changes && m.inputs.sizeIs <= 2) {
      val out = steps.pair(steps.pair(m.gives, state), steps.traces(state)).asInstanceOf[FrSpec[Any]]
      val schedule = FrSpec.map[Any](FrSpec[BigInt], state)
      lifted(m, Shape("_among", (m.named, state) :: ("between", schedule) :: m.params, out))(xs =>
        others(m, xs, out))
    }

  /** What the class holds in a field: a function of the class's state, the field's part of it. */
  def held(cls: Symbol, field: Symbol): Defined[?] =
    val of = c.structureOf(cls.typeRef.memberType(field)).fold(cls.typeRef.memberType(field))(_.typeRef)
    val m = Member(cls, field, Nil, Select(This(cls), field), of)
    lifted(m, Shape("_held", List((m.named, state)), m.gives))(xs => alone(m, xs.head, Nil, m.gives))

  private def alone(m: Member, self: DTerm[Any], given_ : List[DTerm[Any]], out: LeanType[Any]): DTerm[Any] =
    if !m.changes then c.read(m.body, m.result)(using m.env(self, given_))
    else steps.run(m.body, m.result, m.cls)((v, w) => steps.packed(v)(using w))(
      using steps.Walk(m.env(self, given_), 0, None, steps.Ports(m.cls, Map.empty, false), out))

  /** Among other calls: of a class that holds no structure, the member run as one step; else each call of a held
    * structure a step, the schedule read before each but the first.
    */
  private def others(m: Member, inputs: List[DTerm[Any]], out: LeanType[Any]): DTerm[Any] =
    val (self, between, given_) = (inputs.head, inputs(1), inputs.drop(2))
    given LeanType[Any] = state
    if c.isStore(m.cls.typeRef) then
      val did = alone(m, self, given_, steps.pair(m.gives, state).asInstanceOf[LeanType[Any]])
      Among.atomic[Any, Any](self, did.asInstanceOf[DTerm[(Any, Any)]])(using m.gives, state).asInstanceOf[DTerm[Any]]
    else
      val start = m.env(self, given_) + ((steps.trace, Among.none[Any].asInstanceOf[DTerm[Any]]))
      steps.run(m.body, m.result, m.cls)((v, w) => Among.ended[Any, Any](v, w.whole,
        w.env(steps.trace).asInstanceOf[DTerm[Among.Traces[Any]]])(using m.gives, state).asInstanceOf[DTerm[Any]])(
        using steps.Walk(start, 0, Some(between), steps.Ports(m.cls, Map.empty, false), out))

  /** A member the class implements with a field (`val limit: BigInt`): the field, read. */
  private def field(cls: Symbol, member: Symbol): Term =
    val f = cls.fieldMember(member.name)
    if f.isNoSymbol then c.refuse(s"the member ${member.name} of ${cls.name}, whose body is not in the TASTy " +
      "read", cls.tree)
    Select(This(cls), f)

  /** The Definition the code is: of up to four inputs, the state the first. */
  private def lifted(m: Member, shape: Shape)(body: List[DTerm[Any]] => DTerm[Any]): Defined[?] =
    import shape.{out, params}
    val name = DefName(steps.decapitalized(m.cls.name) + "_" + m.member.name + shape.suffix)
    val at = WrittenAt.in(Source.path(m.cls.pos.fold("")(p => Source.relative(p.sourceFile.path))))
    val written = AsWritten(m.member.pos.flatMap(_.sourceCode).getOrElse(m.member.name), params.map(_._1))
    val made = c.once(params)(body)
    params.map(_._2) match
      case List(a)             => Lifting.one[Any, Any](name, at, written)(x => made(List(x)))(using a, out)
      case List(a, b)          =>
        Lifting.two[Any, Any, Any](name, at, written)((x, y) => made(List(x, y)))(using a, b, out)
      case List(a, b, d)       =>
        Lifting.three[Any, Any, Any, Any](name, at, written)((x, y, z) => made(List(x, y, z)))(using a, b, d, out)
      case List(a, b, d, e)    => Lifting.four[Any, Any, Any, Any, Any](name, at, written)((x, y, z, u) =>
        made(List(x, y, z, u)))(using a, b, d, e, out)
      case _                   => c.refuse(s"the member ${m.member.name}, of more than three inputs", m.cls.tree)

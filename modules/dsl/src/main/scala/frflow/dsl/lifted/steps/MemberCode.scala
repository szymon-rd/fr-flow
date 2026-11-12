package frflow.dsl.lifted.steps

import frflow.core.name.DefName
import frflow.dsl.build.{AsWritten, Source, WrittenAt}
import frflow.dsl.lifted.Lifting
import frflow.dsl.term.Term as DTerm
import frflow.dsl.vocab.Definition as Defined
import scala.quoted.*

/** One member of a class that implements a structure, as code (`StructureLift`): a function of the class's state and
  * the member's inputs, read from the method's body. A member that changes the structure gives its result with the
  * state after it; one that only asks gives its result. A member that changes the structure is also read among
  * other calls (`among`): each call it makes of a structure it holds is a step, before which the others may have
  * left the state as a schedule says; it gives its result and the state after with what each step did.
  */
private[steps] final class MemberCode(val step: StepReader):
  import step.r.q.reflect.*

  /** A member as the class has it: its inputs, its body, and the type of its result. */
  private final case class Member(cls: Symbol, member: Symbol, inputs: List[ValDef], body: Term, result: TypeRepr):
    def changes: Boolean = member.flags.is(Flags.Mutable)
    def env(state: Expr[DTerm[?]], given_ : List[Expr[DTerm[?]]]): step.r.Env =
      step.r.Env.of(((cls, state) :: inputs.map(_.symbol).zip(given_))*)
    /** The state as the code's first input: named as the structure. */
    def state[T: Type]: (String, TypeRepr) =
      (step.decapitalized(step.r.structureOf(cls.typeRef).fold(cls.name)(_.name)), TypeRepr.of[T])
    def given_ : List[(String, TypeRepr)] = inputs.map(i => (i.name, i.tpt.tpe))

  private def memberOf(cls: Symbol, member: Symbol, result: TypeRepr): Member =
    val method = cls.declaredMethod(member.name).headOption.flatMap(step.r.kept)
    Member(cls, member, method.fold(Nil)(_.termParamss.flatMap(_.params)),
      method.map(_.rhs.get).getOrElse(field(cls, member)), result)

  def of[T: Type](cls: Symbol, member: Symbol, result: TypeRepr)(using Quotes): Expr[Defined[?]] =
    val m = memberOf(cls, member, result)
    val gives = if !m.changes then result else result.asType match
      case '[v] => TypeRepr.of[(v, T)]
    gives.asType match
      case '[out] => lifted[out](m, "", m.state[T] :: m.given_)(xs => alone[out](m, xs.head, xs.tail))
        .asInstanceOf[Expr[Defined[?]]]

  /** The member among other calls, where it changes the structure and has at most two inputs. */
  def among[T: Type](cls: Symbol, member: Symbol, result: TypeRepr)(using Quotes): Option[Expr[Defined[?]]] =
    val m = memberOf(cls, member, result)
    Option.when(m.changes && m.inputs.sizeIs <= 2)(result.asType match
      case '[v] => lifted[((v, T), Among.Traces[T])](m, "_among",
        m.state[T] :: ("between", TypeRepr.of[Map[BigInt, T]]) :: m.given_)(xs =>
        others[v, T](m, xs.head.asExprOf[DTerm[T]], xs(1), xs.drop(2))).asInstanceOf[Expr[Defined[?]]])

  private def alone[Out: Type](m: Member, state: Expr[DTerm[?]], given_ : List[Expr[DTerm[?]]])(using Quotes)
      : Expr[DTerm[Out]] =
    if !m.changes then step.r.readAs[Out](m.body)(using m.env(state, given_))
    else step.run[Out](m.body, m.result, m.cls)((v, w) => step.packed(v, m.result)(using w).asExprOf[DTerm[Out]])(
      using step.Walk(m.env(state, given_), 0, None, step.Ports(m.cls, Map.empty, false)))

  /** Among other calls: of a class that holds no structure, the member run as one step; else each call of a held
    * structure a step, the schedule read before each but the first.
    */
  private def others[V: Type, T: Type](m: Member, state: Expr[DTerm[T]], between: Expr[DTerm[?]],
      given_ : List[Expr[DTerm[?]]])(using Quotes): Expr[DTerm[((V, T), Among.Traces[T])]] =
    val (sv, st) = (step.r.spec[V](m.cls.tree), step.r.spec[T](m.cls.tree))
    if step.r.isStore(m.cls.typeRef) then
      '{ Among.atomic[V, T]($state, ${ alone[(V, T)](m, state, given_) })(using $sv, $st) }
    else
      val start = m.env(state, given_) + ((step.trace, '{ Among.none[T](using $st) }))
      step.run[((V, T), Among.Traces[T])](m.body, m.result, m.cls)((v, w) => '{ Among.ended[V, T](
        ${ v.asExprOf[DTerm[V]] }, ${ w.whole.asExprOf[DTerm[T]] },
        ${ w.env(step.trace).asExprOf[DTerm[Among.Traces[T]]] })(using $sv, $st) })(
        using step.Walk(start, 0, Some((between, state)), step.Ports(m.cls, Map.empty, false)))

  /** A member the class implements with a field (`val limit: BigInt`): the field, read. */
  private def field(cls: Symbol, member: Symbol): Term =
    val f = cls.fieldMember(member.name)
    if f.isNoSymbol then step.r.refuse(s"the member ${member.name} of ${cls.name}, whose body the compiler did " +
      "not keep (compile with `-Yretain-trees`)", cls.tree)
    Select(This(cls), f)

  /** The code's name (the class's and the member's), where it is written, and its Scala. */
  private def named(m: Member, suffix: String, params: List[String])(using Quotes)
      : (Expr[DefName], Expr[WrittenAt], Expr[AsWritten]) =
    ('{ DefName(${ Expr(step.decapitalized(m.cls.name) + "_" + m.member.name + suffix) }) },
      '{ WrittenAt.in(Source.path(${ Expr(m.cls.pos.fold("")(p => Source.relative(p.sourceFile.path))) })) },
      '{ AsWritten(${ Expr(m.member.pos.flatMap(_.sourceCode).getOrElse(m.member.name)) }, ${ Expr(params) }) })

  /** The Definition the code is: of up to four inputs, the state the first. */
  private def lifted[Out: Type](m: Member, suffix: String, params: List[(String, TypeRepr)])(
      body: List[Expr[DTerm[?]]] => Quotes ?=> Expr[DTerm[Out]])(using Quotes): Expr[Any] =
    val (name, at, written) = named(m, suffix, params.map(_._1))
    val (so, site) = (step.r.spec[Out](m.cls.tree), m.cls.tree)
    params.map(_._2.asType) match
      case List('[a])       =>
        '{ Lifting.one[a, Out]($name, $at, $written)((x: DTerm[a]) => ${ body(List('x)) })(using
          ${ step.r.spec[a](site) }, $so) }
      case List('[a], '[b]) =>
        '{ Lifting.two[a, b, Out]($name, $at, $written)((x: DTerm[a], y: DTerm[b]) => ${ body(List('x, 'y)) })(
          using ${ step.r.spec[a](site) }, ${ step.r.spec[b](site) }, $so) }
      case _                => wide[Out](m, suffix, params)(body)

  /** The same of three or four inputs. */
  private def wide[Out: Type](m: Member, suffix: String, params: List[(String, TypeRepr)])(
      body: List[Expr[DTerm[?]]] => Quotes ?=> Expr[DTerm[Out]])(using Quotes): Expr[Any] =
    val (name, at, written) = named(m, suffix, params.map(_._1))
    val (so, site) = (step.r.spec[Out](m.cls.tree), m.cls.tree)
    params.map(_._2.asType) match
      case List('[a], '[b], '[c])       =>
        '{ Lifting.three[a, b, c, Out]($name, $at, $written)((x: DTerm[a], y: DTerm[b], z: DTerm[c]) =>
          ${ body(List('x, 'y, 'z)) })(using ${ step.r.spec[a](site) }, ${ step.r.spec[b](site) },
          ${ step.r.spec[c](site) }, $so) }
      case List('[a], '[b], '[c], '[d]) =>
        '{ Lifting.four[a, b, c, d, Out]($name, $at, $written)((x: DTerm[a], y: DTerm[b], z: DTerm[c],
          u: DTerm[d]) => ${ body(List('x, 'y, 'z, 'u)) })(using ${ step.r.spec[a](site) },
          ${ step.r.spec[b](site) }, ${ step.r.spec[c](site) }, ${ step.r.spec[d](site) }, $so) }
      case _                            =>
        step.r.refuse(s"the member ${m.member.name}, of more than three inputs", site)

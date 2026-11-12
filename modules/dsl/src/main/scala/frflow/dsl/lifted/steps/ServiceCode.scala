package frflow.dsl.lifted.steps

import frflow.core.name.DefName
import frflow.dsl.build.{AsWritten, Source, WrittenAt}
import frflow.dsl.lifted.Lifting
import frflow.dsl.term.Term as DTerm
import frflow.dsl.vocab.Definition as Defined
import scala.quoted.*

/** One member of a class that implements a service, as code (`ServiceLift`): a function of the class's state and
  * the member's inputs, read from the method's body. A member that changes the service gives its result with the
  * state after it; one that only asks gives its result.
  */
private[steps] final class ServiceCode(val step: StepReader):
  import step.r.q.reflect.*

  def of[T: Type](cls: Symbol, member: Symbol, result: TypeRepr)(using Quotes): Expr[Defined[?]] =
    val changes = member.flags.is(Flags.Mutable)
    val method = cls.declaredMethod(member.name).headOption.flatMap(step.r.kept)
    val inputs = method.fold(Nil)(_.termParamss.flatMap(_.params))
    val body = method.map(_.rhs.get).getOrElse(field(cls, member))
    val gives = if !changes then result else result.asType match
      case '[v] => TypeRepr.of[(v, T)]
    def read[Out: Type](state: Expr[DTerm[T]], given_ : List[Expr[DTerm[?]]])(using Quotes): Expr[DTerm[Out]] =
      val env = step.r.Env.of(((cls, state) :: inputs.map(_.symbol).zip(given_))*)
      if !changes then step.r.readAs[Out](body)(using env)
      else step.run[Out](body, result, cls)((v, w) => step.packed(v, result)(using w).asExprOf[DTerm[Out]])(
        using step.Walk(env, 0, None, step.Ports(cls, Map.empty, false)))
    gives.asType match
      case '[out] => lifted[T, out](cls, member, inputs)((s, xs) => read[out](s, xs)).asInstanceOf[Expr[Defined[?]]]

  /** A member the class implements with a field (`val limit: BigInt`): the field, read. */
  private def field(cls: Symbol, member: Symbol): Term =
    val f = cls.fieldMember(member.name)
    if f.isNoSymbol then step.r.refuse(s"the member ${member.name} of ${cls.name}, whose body the compiler did " +
      "not keep (compile with `-Yretain-trees`)", cls.tree)
    Select(This(cls), f)

  /** The code's name (the class's and the member's), where it is written, and its Scala. */
  private def named(cls: Symbol, member: Symbol, inputs: List[ValDef])(using Quotes)
      : (Expr[DefName], Expr[WrittenAt], Expr[AsWritten]) =
    val service = step.r.serviceOf(cls.typeRef).fold(cls.name)(_.name)
    ('{ DefName(${ Expr(step.decapitalized(cls.name) + "_" + member.name) }) },
      '{ WrittenAt.in(Source.path(${ Expr(cls.pos.fold("")(p => Source.relative(p.sourceFile.path))) })) },
      '{ AsWritten(${ Expr(member.pos.flatMap(_.sourceCode).getOrElse(member.name)) },
        ${ Expr(step.decapitalized(service) :: inputs.map(_.name)) }) })

  /** The Definition the code is: of the state and up to three inputs. */
  private def lifted[T: Type, Out: Type](cls: Symbol, member: Symbol, inputs: List[ValDef])(
      body: (Expr[DTerm[T]], List[Expr[DTerm[?]]]) => Quotes ?=> Expr[DTerm[Out]])(using Quotes): Expr[Any] =
    val (name, at, written) = named(cls, member, inputs)
    val (st, so) = (step.r.spec[T](cls.tree), step.r.spec[Out](cls.tree))
    def run(s: Expr[DTerm[T]], xs: List[Expr[DTerm[?]]])(using Quotes): Expr[DTerm[Out]] = body(s, xs)
    inputs.map(_.tpt.tpe.asType) match
      case Nil                          =>
        '{ Lifting.one[T, Out]($name, $at, $written)((s: DTerm[T]) => ${ run('s, Nil) })(using $st, $so) }
      case List('[a])                   =>
        '{ Lifting.two[T, a, Out]($name, $at, $written)((s: DTerm[T], x: DTerm[a]) => ${ run('s, List('x)) })(
          using $st, ${ step.r.spec[a](cls.tree) }, $so) }
      case List('[a], '[b])             =>
        '{ Lifting.three[T, a, b, Out]($name, $at, $written)((s: DTerm[T], x: DTerm[a], y: DTerm[b]) =>
          ${ run('s, List('x, 'y)) })(using $st, ${ step.r.spec[a](cls.tree) }, ${ step.r.spec[b](cls.tree) }, $so) }
      case List('[a], '[b], '[c])       =>
        '{ Lifting.four[T, a, b, c, Out]($name, $at, $written)((s: DTerm[T], x: DTerm[a], y: DTerm[b],
          z: DTerm[c]) => ${ run('s, List('x, 'y, 'z)) })(using $st, ${ step.r.spec[a](cls.tree) },
          ${ step.r.spec[b](cls.tree) }, ${ step.r.spec[c](cls.tree) }, $so) }
      case _                            =>
        step.r.refuse(s"the member ${member.name}, of more than three inputs", cls.tree)

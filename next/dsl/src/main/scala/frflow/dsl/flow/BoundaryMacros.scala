package frflow.dsl.flow

import cats.{Functor, Id, MonadThrow}
import cats.syntax.all.*
import frflow.core.expr.Binder
import frflow.core.name.{BoundaryName, OpName, VarId}
import frflow.core.ty.Ty
import frflow.core.vocab.{Fails, ModelOp, OpSig}
import frflow.dsl.build.Declarations
import frflow.dsl.flow.BoundaryTrait.Op
import frflow.dsl.term.{LeanType, Term}
import scala.quoted.*

/** `BoundaryOps[B]` from the trait's declared methods: each method's parameters and result with their `LeanType`s
  * summoned, and the three instances, each method one line (a call recorded, a call by name, a call lifted).
  */
object BoundaryMacros:
  def derived[B[_[_], _[_]]: Type](using Quotes): Expr[BoundaryOps[B]] =
    val read = BoundaryTrait.ops[B]
    val types = Expr.ofList(read.flatMap(o => o.params.map(_._2) ++ o.result).map(leanType))
    '{
      new BoundaryOps[B]:
        def className: String = ${ Expr(quotes.reflect.TypeRepr.of[B].typeSymbol.name) }
        def ops: List[OpSig] = ${ Expr.ofList(read.map(sig)) }
        def declares: Declarations = $types.foldMap(_.declares)
        def recording(name: BoundaryName): B[Recorded, Term] = ${ recorded[B](read, 'name) }
        def call[F[_]: Functor](adapter: B[F, Id], op: OpName, args: List[Any]): F[Any] =
          ${ called[B, F](read, 'adapter, 'op, 'args) }
        def lifted[F[_]: MonadThrow](adapter: B[F, Id], values: Terms, fails: Option[Fails]): B[F, Term] =
          ${ liftedOf[B, F](read, 'adapter, 'values, 'fails) }
        def model(instance: B[Recorded, Term]): List[ModelOp] = ${ modelled[B](read, 'instance) }
    }

  private def sig(o: Op)(using Quotes): Expr[OpSig] =
    val params = Expr.ofList(o.params.map((n, t) => '{ (${ Expr(n) }, ${ leanType(t) }.ty) }))
    '{ OpSig(OpName(${ Expr(o.name) }), $params, ${ o.result.fold('{ Ty.Unit })(t => '{ ${ leanType(t) }.ty }) }) }

  /** Each operation a recorded call; one giving nothing is the call, its unit result dropped (the reading hands on
    * `()` for it, so the function takes any value).
    */
  private def recorded[B[_[_], _[_]]: Type](ops: List[Op], name: Expr[BoundaryName])(using q: Quotes)
      : Expr[B[Recorded, Term]] =
    import q.reflect.asTerm
    BoundaryInstance.of[B, Recorded, Term](ops) { (o, args) =>
      val terms = Expr.ofList(args.map(_.asExprOf[Term[?]]))
      val op = Expr(o.name)
      o.result match
        case Some('[r]) => '{ Recorded.Call[r]($name, OpName($op), $terms, ${ typed[r] }) }.asTerm
        case _          => '{ Recorded.Bind(Recorded.Call[Unit]($name, OpName($op), $terms, LeanType[Unit]),
            (_: Any) => Recorded.Pure(())) }.asTerm
    }

  /** An adapter's operation called by name on values of its parameters' types. */
  private def called[B[_[_], _[_]]: Type, F[_]: Type](ops: List[Op], adapter: Expr[B[F, Id]], op: Expr[OpName],
      args: Expr[List[Any]])(using Quotes): Expr[F[Any]] =
    val functor = summonOrAbort[Functor[F]]
    ops.foldRight[Expr[F[Any]]]('{ throw IllegalArgumentException(s"FrFlow bug: no operation ${$op.value}") }) {
      (o, rest) =>
        // The model tests call an operation with values drawn at its parameters' types, as `ops` declares them.
        val values = o.params.map(_._2).zipWithIndex.map((t, i) => t match
          case '[a] => '{ $args(${ Expr(i) }).asInstanceOf[a] })
        val one = o.result match
          case Some('[r]) => '{ $functor.widen[r, Any](${ invoke[F[r]](adapter, o, values) }) }
          case _          => '{ $functor.widen[Unit, Any](${ invoke[F[Unit]](adapter, o, values) }) }
        '{ if $op.value == ${ Expr(o.name) } then $one else $rest }
    }

  /** The adapter as programs call it: each argument its term's value, evaluated in `F` before the call; the call,
    * its failures as the boundary says it fails (`BoundaryOps.failures`); each result its value's term.
    */
  private def liftedOf[B[_[_], _[_]]: Type, F[_]: Type](ops: List[Op], adapter: Expr[B[F, Id]], values: Expr[Terms],
      fails: Expr[Option[Fails]])(using q: Quotes): Expr[B[F, Term]] =
    import q.reflect.asTerm
    val monad = summonOrAbort[MonadThrow[F]]
    BoundaryInstance.of[B, F, Term](ops) { (o, args) =>
      def call[R: Type](plain: List[Expr[Any]]): Expr[F[R]] = '{ BoundaryOps.failures[F, R]($fails, $values.fail)(
        $monad.flatten($monad.catchNonFatal(${ invoke[F[R]](adapter, o, plain) })))(using $monad) }
      def deferred[R: Type](e: Expr[F[R]]): q.reflect.Term = '{ $monad.flatMap($monad.unit)(_ => $e) }.asTerm
      val typedArgs = o.params.map(_._2).zip(args.map(_.asExpr))
      o.result match
        case Some('[r]) => deferred(evaluated[F, Term[r]](monad, values, typedArgs, Nil)(plain =>
          '{ $monad.map(${ call[r](plain) })(x => $values.term[r](x)(using ${ typed[r] })) }))
        case _ => deferred(evaluated[F, Unit](monad, values, typedArgs, Nil)(call[Unit]))
    }

  /** Each argument's value, in `F`, one after the other, and then `k` of them. */
  private def evaluated[F[_]: Type, R: Type](monad: Expr[MonadThrow[F]], values: Expr[Terms],
      args: List[(Type[?], Expr[Any])], done: List[Expr[Any]])(k: List[Expr[Any]] => Expr[F[R]])(using Quotes)
      : Expr[F[R]] =
    args match
      case Nil             => k(done.reverse)
      case (ty, t) :: rest => ty match
        case '[a] => '{ $monad.flatMap($monad.catchNonFatal($values.value[a](${ t.asExprOf[Term[a]] })))((x: a) =>
            ${ evaluated[F, R](monad, values, rest, 'x :: done)(k) }) }

  /** Each operation's steps on the model, from its parameters' variables (levels from 0, named as the trait names
    * them).
    */
  private def modelled[B[_[_], _[_]]: Type](ops: List[Op], instance: Expr[B[Recorded, Term]])(using Quotes)
      : Expr[List[ModelOp]] =
    Expr.ofList(ops.map { o =>
      val binders = o.params.zipWithIndex.map { case ((n, t), i) =>
        '{ Binder(VarId.level(${ Expr(i) }), ${ Expr(n) }, ${ leanType(t) }.ty) } }
      val free = o.params.map(_._2).zip(binders).map((t, b) => t match
        case '[a] => '{ Term.free[a]($b)(using ${ typed[a] }) })
      val steps = o.result match
        case Some('[r]) => '{ ReadRecording.steps(${ invoke[Recorded[Term[r]]](instance, o, free) })._1 }
        case _          => '{ ReadRecording.steps(${ invoke[Recorded[Unit]](instance, o, free) })._1 }
      '{ ModelOp(OpName(${ Expr(o.name) }), ${ Expr.ofList(binders) }, $steps) }
    })

  /** `receiver.op(args…)`, typed `R`. */
  private def invoke[R: Type](receiver: Expr[Any], o: Op, args: List[Expr[Any]])(using Quotes): Expr[R] =
    import quotes.reflect.*
    val select = Select.unique(receiver.asTerm, o.name)
    (if o.parameterless then select else Apply(select, args.map(_.asTerm))).asExprOf[R]

  private def leanType(t: Type[?])(using Quotes): Expr[LeanType[?]] = t match
    case '[a] => typed[a]

  /** A type's `LeanType`, or the standard refusal: the type is not a domain type yet. */
  private def typed[A: Type](using Quotes): Expr[LeanType[A]] =
    import quotes.reflect.*
    val name = TypeRepr.of[A].show(using Printer.TypeReprShortCode)
    Expr.summon[LeanType[A]].getOrElse(report.errorAndAbort(
      s"FrFlow: $name is not a domain type yet: add `derives LeanType` to its declaration"))

  private def summonOrAbort[X: Type](using Quotes): Expr[X] =
    Expr.summon[X].getOrElse(quotes.reflect.report.errorAndAbort(s"FrFlow: no ${Type.show[X]} for a boundary's " +
      "operation"))

package frflow.dsl.kb

import cats.syntax.all.*
import frflow.core.code.{Attachment, Code}
import frflow.core.name.RelPath
import frflow.core.ty.Ty
import frflow.dsl.build.{Declarations, Deferred, Fault, Site, Source}
import frflow.dsl.node.Spans
import frflow.dsl.service.{ServiceDefinition, ServiceImplementation}
import frflow.dsl.term.Reify
import frflow.dsl.vocab.Definition

/** What gives each Definition its meaning (owner §15), one pattern, written once in the FrModel and checked
  * against every claim mentioning the Definition: `implementProven` (a define or a program; Lean proves it, `impl`),
  * `implementTested` (plain Scala, tested on generated cases; of operations on a state, the Scala of their model's
  * operations, tested against it on generated runs), `implementValue` (a value fixed in the model),
  * `implementProvided` (a value provided where the code runs). Only a Definition takes any of them, and only one
  * that has no meaning where it is written: a Declaration has no meaning to give.
  */
object Implementing:
  extension (kb: FrModel)
    /** `d` is `proven` (a `define` or a `program`), which Lean proves meets each claim mentioning `d` (`impl`); the
      * files `proven` is written in are the model's own.
      */
    inline def implementProven[F](d: Definition[F])(proven: Definition[F]): FrModel =
      Implementing.proven(kb, d, proven, Spans.relative(Source.file))

    /** Plain Scala for the Definitions `ds`, as the next argument list says (`Tested`): the first one's, built from
      * the values it is given and calling the others (`implementTested(granted)(env => …)`), or the operations on one
      * state's, tested against their model (`implementTested(inRoom, add)(start = …, observe = …)(t => …)`). Each
      * Definition's type is read here, so the Scala is typed by it.
      */
    transparent inline def implementTested(inline ds: Definition[?]*): Any = ${ TestedMacro.of('kb, 'ds) }

    /** `d` is `value`, fixed in the model. */
    inline def implementValue[A](d: Definition[A])(value: A): FrModel =
      val at = Spans.relative(Source.file)
      Implementing.attach(kb, d, Reify(d.leanType, value).fold(Deferred.failed(Site.Meaning(d.name), _),
        v => Deferred.pure(Attachment(Code.Valued(v), at))))

    /** The values of `ds` are provided where the code runs: bound by an example, drawn by a test, passed in
      * production; Lean states every claim for each.
      */
    inline def implementProvided(ds: Definition[?]*): FrModel =
      ds.foldLeft(kb)((k, d) =>
        Implementing.attach(k, d, Deferred.pure(Attachment(Code.Provided, Spans.relative(Source.file)))))

  /** `d` given `proven`: a define or a program; or, of a service, the class that implements it, each member's
    * Definition given the member's code, and of a member that changes the service, its Definition among other
    * calls given that code. Each is kept where a statement mentions it. The service itself has no value in the
    * model: a claim on it is said of the service in every state (`Serving`).
    */
  def proven(kb: FrModel, d: Definition[?], proven: Definition[?], at: RelPath): FrModel = (d, proven) match
    case (service: ServiceDefinition[?], given_ : ServiceImplementation[?]) =>
      val members = service.members.map(m => service.member(m.name) -> given_.code.get(m.name))
      val among = service.members.filter(_.changes).map(m =>
        service.among(m.name) -> given_.code.get(ServiceImplementation.among(m.name)))
      (members ++ among).foldLeft(kb) { case (k, (symbol, read)) =>
        k.attachWhenMentioned(symbol.name, declared(symbol, code(symbol, read, at).andThen(a =>
          Deferred((given_.state.declares, a).validNec))))
      }
    case _                                                                  => attach(kb, d, code(d, Some(proven), at))

  private def code(d: Definition[?], proven: Option[Definition[?]], at: RelPath): Deferred[Attachment] =
    proven.flatMap(p => p.onTheSpot.map(p -> _)).fold(Deferred.failed(Site.Meaning(d.name),
      Fault.NotProvenCode(proven.fold(d.name.value)(_.name.value)))) { (p, spot) =>
      Deferred((Declarations.define(spot.name, spot.lambda) |+| p.at.declares(p.name.value),
        Attachment(spot.code, at)).validNec)
    }

  /** The meaning given `d`, unless `d` has its own where it is written; a code-only `d` declared with it. */
  def attach(kb: FrModel, d: Definition[?], a: Deferred[Attachment]): FrModel = kb.attach(d.name, declared(d, a))

  private def declared(d: Definition[?], a: Deferred[Attachment]): Deferred[Attachment] =
    d.onTheSpot.fold(a.andThen(x => Deferred((d.declares, x).validNec)))(_ =>
      Deferred.failed(Site.Meaning(d.name), Fault.MeantWhereWritten(d.name.value)))

  /** How many inputs plain code of this type takes. */
  def arity(ty: Ty): Int = ty match
    case Ty.FnOf(ins, _) => ins.size
    case _               => 0

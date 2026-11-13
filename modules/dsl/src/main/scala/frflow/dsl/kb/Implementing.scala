package frflow.dsl.kb

import cats.syntax.all.*
import frflow.core.code.{Attachment, Code}
import frflow.core.name.RelPath
import frflow.core.ty.Ty
import frflow.dsl.build.{Declarations, Deferred, Fault, Site}
import frflow.dsl.lifted.steps.StructureCode
import frflow.dsl.structure.StructureDeclaration
import frflow.dsl.vocab.{Declaration, Definition}

/** What a Definition listed in a FrModel gives it (`Defining`): each word's meaning, once. Only a word with no
  * meaning where it is written takes one.
  */
object Implementing:
  /** `d` given `proven`: a define or a program; or, of a structure, the class that implements it, each member's
    * Definition given the member's code, and of a member that changes the structure, its Definition among other
    * calls given that code, whether or not a statement mentions it; and of each structure the class holds, the
    * word that is what it holds given the field read. The structure itself has no value in the model: a claim on
    * it is said of the structure in every state (`Standing`).
    */
  def proven(kb: FrModel, d: Declaration[?], proven: Definition[?], at: RelPath): FrModel = (d, proven) match
    case (structure: StructureDeclaration[?], given_ : StructureCode[?]) =>
      val members = structure.members.map(m => structure.member(m.name) -> given_.code.get(m.name))
      val among = structure.members.filter(_.changes).map(m =>
        structure.among(m.name) -> given_.code.get(StructureCode.among(m.name)))
      val held = given_.held.map(h => h.word.asInstanceOf[Definition[Any]] -> Option(h.code))
      val holding = kb.holding(given_.held.map(h =>
        FrModel.Holding(structure.name, h.part, h.word.name, h.members)(h.word)))
      (members ++ among ++ held).foldLeft(holding) { case (k, (symbol, read)) =>
        k.attachMember(symbol.name, declared(symbol, code(symbol, read, at).andThen(a =>
          Deferred((given_.state.declares |+| symbol.notes.declares, a).validNec))))
      }
    case _                                                                   =>
      attach(kb, d.word, code(d.word, Some(proven), at))

  /** A structure provided where the code runs: each member's word provided, as a value is (`Code.Provided`). */
  def provided(kb: FrModel, structure: StructureDeclaration[?], at: RelPath): FrModel =
    structure.members.map(m => structure.member(m.name)).foldLeft(kb)((k, word) =>
      k.attachMember(word.name, declared(word, Deferred.pure(Attachment(Code.Provided, at)))))

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

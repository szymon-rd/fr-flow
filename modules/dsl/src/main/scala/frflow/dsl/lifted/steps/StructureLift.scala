package frflow.dsl.lifted.steps

import frflow.core.name.TypeName
import frflow.core.ty.Ty
import frflow.dsl.lifted.{FrSpec, NotRead, Reader, Tasty}
import frflow.dsl.structure.{StructureDeclaration, StructureMacros, Structures}
import frflow.dsl.vocab.Definition as Defined
import scala.quoted.*

/** `lifted[RecordedLimits]`: a class that implements a structure, read member by member. Its state is the record of
  * its constructor's fields; each member's body is read into a function of that record: what it gives, and, of a
  * member that changes the structure, the record after it. A class that holds structures is given the word of each,
  * in the order its constructor takes them (`lifted[StreamPaymentHandler](limits, ledger, offsets)`): a call of a
  * held structure's member is a call of that word's, so the class is proven from the claims on the structures it is
  * made with.
  */
object StructureLift:
  /** The class named `name`, read from its TASTy as the model is built (`ReadClass`): what gives its code from the
    * words given for the structures it holds. `words` are those words, checked here against what the class
    * holds.
    */
  def staged(name: String, words: List[StructureDeclaration[?]])(using q: Quotes)
      : Expr[List[StructureDeclaration[?]] => StructureCode[?]] =
    val plain = Reader(q, reading)
    import plain.q.reflect.*
    val cls = Symbol.requiredClass(name)
    Tasty.load(plain.q)(cls)
    val trt = implemented(plain)(cls)
    given_(plain)(cls, words)
    trt.typeRef.asType match
      case '[t] => '{ (given_ : List[StructureDeclaration[?]]) =>
        ${ typed[t](q, cls, List.tabulate(words.size)(i => '{ given_(${ Expr(i) }) })) } }

  /** A reading of a compiled class, as the model is built: no structure known yet. */
  private val reading: Structures = Structures.none.copy(staged = true)

  /** The class read, typed by the structure `T` it implements. */
  private def typed[T: Type](q: Quotes, implementing: Any, words: List[Expr[StructureDeclaration[?]]])(using Quotes)
      : Expr[StructureCode[T]] =
    val plain = Reader(q, reading)
    import plain.q.reflect.*
    val cls = implementing.asInstanceOf[Symbol]
    val trt = implemented(plain)(cls)
    val held = holding(plain)(cls)
    val traits = (trt :: held.map(_._2)).map(_.fullName).toSet
    val wiring = held.map(_._1.name).zip(words.map(w => (w: Expr[Any]))).toMap
    val knowing = Reader(q, reading.copy(traits = traits))
    '{ val state: FrSpec[T] = ${ StructureRecord(knowing).of[T](cls, trt.name) }
       new StructureCode[T](${ Expr(cls.name) }, state,
         ${ codes[T](q, cls, reading.copy(Map(trt.fullName -> 'state), wiring, traits)) },
         ${ holds[T](q, cls, reading.copy(Map(trt.fullName -> 'state), wiring, traits), 'state) }) }

  /** The fields of a class that hold structures, each with its structure, in the order the constructor takes
    * them.
    */
  private def holding(r: Reader)(cls: r.q.reflect.Symbol): List[(r.q.reflect.Symbol, r.q.reflect.Symbol)] =
    r.stateFields(cls).flatMap(f => r.declarableOf(cls.typeRef.memberType(f)).map(f -> _))

  /** Refused unless `words` are one for each structure the class holds, each a word of its field's structure. */
  private def given_(r: Reader)(cls: r.q.reflect.Symbol, words: List[StructureDeclaration[?]]): Unit =
    val held = holding(r)(cls)
    val asked = s"`lifted[${cls.name}](${held.map(_._1.name).mkString(", ")})`"
    if held.size != words.size then NotRead.raise(using r.q)(true, s"FrFlow: ${cls.name} holds ${held.size} " +
      s"structures and is given ${words.size} words: give the word of each, in order ($asked)", None)
    held.zip(words).foreach { case ((f, structure), w) =>
      if w.leanType.ty != Ty.Data(TypeName(structure.name)) then NotRead.raise(using r.q)(true, s"FrFlow: " +
        s"${cls.name} holds ${f.name}, a ${structure.name}, and is given ${w.name.value}, which is no word of " +
        s"that structure ($asked)", None)
    }

  /** `limits.holding(RecordedLimits(BigInt(100), Nil))`: the record an object of a class that implements a
    * structure has as a state of it: its constructor's fields, an object among them that implements a structure
    * the record of that object's own class.
    */
  def state(made: Any)(using q: Quotes): Expr[FrSpec[?]] =
    val plain = Reader(q, reading)
    import plain.q.reflect.*
    val cls = Symbol.requiredClass(made.getClass.getName.replace('$', '.'))
    val trt = implemented(plain)(cls)
    val held = holding(plain)(cls).map((f, structure) =>
      structure.fullName -> (state(StructureType.read(made, f.name)): Expr[Any])).toMap
    trt.typeRef.asType match
      case '[t] =>
        StructureRecord(Reader(q, reading.copy(records = held, traits = held.keySet + trt.fullName)))
          .of[t](cls, trt.name)

  /** The structure a class implements. */
  private def implemented(r: Reader)(cls: r.q.reflect.Symbol): r.q.reflect.Symbol =
    r.declarableOf(cls.typeRef).filter(_ != cls).getOrElse(NotRead.raise(using r.q)(r.structures.staged,
      s"FrFlow: ${cls.name} implements no structure: a trait of the developer's whose members are over domain " +
        "types", None))

  /** What the class holds: of each field given a word, that word's part of the class's state. */
  private def holds[T: Type](q: Quotes, cls: Any, structures: Structures, state: Expr[FrSpec[T]])(using Quotes)
      : Expr[List[StructureCode.Held]] =
    val code = MemberCode(StepReader(Reader(q, structures), None))
    import code.step.r.q.reflect.*
    val impl = cls.asInstanceOf[Symbol]
    Expr.ofList(structures.wiring.toList.map((field, word) =>
      '{ val part = ${ word.asExprOf[StructureDeclaration[?]] }
         StructureCode.Held(part.name, part.words, StructureDeclaration.held($state, part.name, part.leanType),
           ${ code.held[T](impl, impl.fieldMember(field)) }) }))

  /** Each member's code, by the member's name. */
  private def codes[T: Type](q: Quotes, cls: Any, structures: Structures)(using Quotes)
      : Expr[Map[String, Defined[?]]] =
    val code = MemberCode(StepReader(Reader(q, structures), None))
    import code.step.r.q.reflect.*
    val impl = cls.asInstanceOf[Symbol]
    val all = StructureMacros.members(using code.step.r.q)(TypeRepr.of[T]).flatMap((m, _, result) =>
      '{ (${ Expr(m.name) }, ${ code.of[T](impl, m, result) }) } :: code.among[T](impl, m, result).toList.map(c =>
        '{ (${ Expr(StructureCode.among(m.name)) }, $c) }))
    '{ Map[String, Defined[?]](${ Varargs(all) }*) }

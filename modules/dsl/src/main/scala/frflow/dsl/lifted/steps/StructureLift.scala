package frflow.dsl.lifted.steps

import frflow.dsl.lifted.{FrSpec, Reader}
import frflow.dsl.structure.{StructureDeclaration, StructureMacros, Structures}
import frflow.dsl.term.Lift
import frflow.dsl.term.Term as DTerm
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
  def read[C: Type](words: Expr[Seq[StructureDeclaration[?]]])(using q: Quotes): Expr[StructureCode[C]] =
    words match
      case Varargs(given_) => of[C](given_.toList)
      case _               => q.reflect.report.errorAndAbort("FrFlow: lifted is given the words of the structures " +
        "a class holds one by one")

  /** A class that holds no structure. */
  def alone[C: Type](using Quotes): Expr[StructureCode[C]] = of[C](Nil)

  /** The class `C` read, each structure it holds the word given for it. */
  private def of[C: Type](words: List[Expr[StructureDeclaration[?]]])(using q: Quotes): Expr[StructureCode[C]] =
    val plain = Reader(q)
    import plain.q.reflect.*
    val cls = TypeRepr.of[C].typeSymbol
    implemented(plain)(cls).typeRef.asType match
      case '[t] => '{ ${ typed[t](q, cls, words) }.asInstanceOf[StructureCode[C]] } // typed by its class

  /** The same, typed by the structure `T` the class implements. */
  private def typed[T: Type](q: Quotes, implementing: Any, words: List[Expr[StructureDeclaration[?]]])(using Quotes)
      : Expr[StructureCode[T]] =
    val plain = Reader(q)
    import plain.q.reflect.*
    val cls = implementing.asInstanceOf[Symbol]
    val trt = implemented(plain)(cls)
    val held = wired(plain)(cls, words)
    val traits = (trt :: held.map(_._2)).map(_.fullName).toSet
    val wiring = held.map(_._1.name).zip(words.map(w => (w: Expr[Any]))).toMap
    val knowing = Reader(q, Structures(Map.empty, Map.empty, traits))
    '{ val state: FrSpec[T] = ${ StructureRecord(knowing).of[T](cls, trt.name) }
       new StructureCode[T](${ Expr(cls.name) }, state,
         ${ codes[T](q, cls, Structures(Map(trt.fullName -> 'state), wiring, traits)) },
         ${ holds[T](q, cls, Structures(Map(trt.fullName -> 'state), wiring, traits), 'state) }) }

  /** The fields of a class that hold structures, each with its structure, in the order the constructor takes
    * them; or the compile error of words that are not one for each, each a word of its field's structure.
    */
  private def wired(r: Reader)(cls: r.q.reflect.Symbol, words: List[Expr[StructureDeclaration[?]]])(using Quotes)
      : List[(r.q.reflect.Symbol, r.q.reflect.Symbol)] =
    import r.q.reflect.*
    val held = r.stateFields(cls).flatMap(f => r.declarableOf(cls.typeRef.memberType(f)).map(f -> _))
    val asked = s"`lifted[${cls.name}](${held.map(_._1.name).mkString(", ")})`"
    if held.size != words.size then report.errorAndAbort(s"FrFlow: ${cls.name} holds ${held.size} structures and " +
      s"is given ${words.size} words: give the word of each, in order ($asked)")
    held.zip(words).foreach { case ((f, structure), w) => structure.typeRef.asType match
      case '[s] => if !(w.asTerm.tpe <:< TypeRepr.of[StructureDeclaration[s]]) then report.errorAndAbort(
        s"FrFlow: ${cls.name} holds ${f.name}, a ${Type.show[s]}, and is given ${w.show}, which is no word of " +
          s"that structure ($asked)")
    }
    held

  /** `limits.holding(RecordedLimits(BigInt(100), Nil))`: an object of a class that implements a structure, as a state
    * of the structure: the record of its constructor's fields, a structure it is made with the record of the object
    * given for it.
    */
  def held[T: Type, S: Type](structure: Expr[T])(using q: Quotes): Expr[DTerm[S]] =
    import q.reflect.*
    '{ val state = ${ stateOf(q, structure.asTerm) }.asInstanceOf[FrSpec[Any]]
       Lift.constant[Any](StructureType.held(state, $structure))(using state)
         .asInstanceOf[DTerm[S]] } // a state is typed by the structure's name

  private def stateOf(q: Quotes, at: Any)(using Quotes): Expr[FrSpec[?]] =
    val plain = Reader(q)
    import plain.q.reflect.*
    val (cls, args) = made(plain)(at.asInstanceOf[Term])
    val trt = implemented(plain)(cls)
    val held = plain.stateFields(cls).zip(args).flatMap((f, arg) =>
      plain.declarableOf(cls.typeRef.memberType(f)).map(s => s.fullName -> stateOf(q, arg))).toMap
    trt.typeRef.asType match
      case '[t] =>
        StructureRecord(Reader(q, Structures(held, Map.empty, held.keySet + trt.fullName))).of[t](cls, trt.name)

  /** The class an object is made of where it is given, and what its constructor is given. */
  private def made(r: Reader)(structure: r.q.reflect.Term): (r.q.reflect.Symbol, List[r.q.reflect.Term]) =
    import r.q.reflect.*
    r.bare(structure) match
      case Apply(Select(New(tpt), _), args) => (tpt.tpe.typeSymbol, args)
      case other                            => r.refuse("a structure that is not made where it is given " +
        "(`limits.holding(RecordedLimits(…))`)", other)

  /** The structure a class implements. */
  private def implemented(r: Reader)(cls: r.q.reflect.Symbol): r.q.reflect.Symbol =
    r.declarableOf(cls.typeRef).filter(_ != cls).getOrElse(r.q.reflect.report.errorAndAbort(
      s"FrFlow: ${cls.name} implements no structure: a trait of the developer's whose members are over domain types"))

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

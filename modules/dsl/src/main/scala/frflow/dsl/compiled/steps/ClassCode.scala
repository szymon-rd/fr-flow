package frflow.dsl.compiled.steps

import frflow.core.name.TypeName
import frflow.core.ty.Ty
import frflow.dsl.build.Source
import frflow.dsl.compiled.{Compiler, Known}
import frflow.dsl.lifted.{FrSpec, NotRead}
import frflow.dsl.lifted.steps.{StructureCode, StructureType}
import frflow.dsl.structure.{StructureDeclaration, StructureMacros}
import frflow.dsl.term.RocqType
import frflow.dsl.vocab.Definition as Defined
import scala.quoted.Quotes

/** A class that implements a structure, compiled member by member from its TASTy (`lifted[RecordedLimits]`). Its
  * state is the record of its constructor's fields; each member's body is compiled into a function of that
  * record: what it gives, and, of a member that changes the structure, the record after it. A class that holds
  * structures is given the word of each, in the order its constructor takes them: a call of a held structure's
  * member is a call of that word's, so the class is proven from the claims on the structures it is made with.
  */
object ClassCode:
  /** The class named `name`, compiled: `words` are the words of the structures it holds. */
  def of(q: Quotes, name: String, words: List[StructureDeclaration[?]], loader: ClassLoader): StructureCode[Any] =
    val plain = Compiler(q, Known(Map.empty, Map.empty, Set.empty, loader))
    import plain.q.reflect.*
    val cls = Symbol.requiredClass(name)
    val trt = implemented(plain)(cls)
    val held = holding(plain)(cls)
    given_(plain)(cls, held.map((f, s) => (f.name, s.name)), words)
    val traits = (trt :: held.map(_._2)).map(_.fullName).toSet
    val wiring = held.map(_._1.name).zip(words).toMap
    val state = record(Compiler(q, Known(Map.empty, Map.empty, traits, loader)))(cls, trt.name)
    val members = Members(Steps(Compiler(q, Known(Map(trt.fullName -> state), wiring, traits, loader))), state)
    val (all, parts) = codes(members)(cls, trt, wiring)
    new StructureCode[Any](cls.name, state, all, parts)

  /** Each member's code, by the member's name, and what the class holds: of each field given a word, that
    * word's part of the class's state.
    */
  private def codes(members: Members)(implementing: Any, structure: Any,
      wiring: Map[String, StructureDeclaration[?]]): (Map[String, Defined[?]], List[StructureCode.Held]) =
    import members.steps.c.q.reflect.*
    val (cls, trt) = (implementing.asInstanceOf[Symbol], structure.asInstanceOf[Symbol])
    val all = StructureMacros.members(using members.steps.c.q)(trt.typeRef).flatMap((m, _, result) =>
      (m.name -> members.of(cls, m, result)) ::
        members.among(cls, m, result).toList.map(StructureCode.among(m.name) -> _))
    val parts = wiring.toList.map((field, word) => StructureCode.Held(word.name, word.words,
      StructureDeclaration.held(members.state, word.name, word.rocqType),
      members.held(cls, cls.fieldMember(field))))
    (Map[String, Defined[?]](all*), parts)

  /** The record an object of a class that implements a structure has as a state of it: its constructor's fields,
    * an object among them that implements a structure the record of that object's own class.
    */
  def state(q: Quotes, made: Any): FrSpec[Any] =
    val loader = made.getClass.getClassLoader
    val plain = Compiler(q, Known(Map.empty, Map.empty, Set.empty, loader))
    import plain.q.reflect.*
    val cls = Symbol.requiredClass(made.getClass.getName.replace('$', '.'))
    val trt = implemented(plain)(cls)
    val held = holding(plain)(cls).map((f, structure) =>
      structure.fullName -> state(q, StructureType.read(made, f.name))).toMap
    record(Compiler(q, Known(held, Map.empty, held.keySet + trt.fullName, loader)))(cls, trt.name)

  /** The record the state of a class that implements a structure is: named as the structure, a field for each of
    * the class's constructor's, in order.
    */
  private def record(c: Compiler)(implementing: Any, name: String): FrSpec[Any] =
    import c.q.reflect.*
    val cls = implementing.asInstanceOf[Symbol]
    val fields = c.stateFields(cls)
    val names = fields.map(_.name)
    StructureType.record[Any]((name, cls.fullName, cls.pos.map(p => Source.relative(p.sourceFile.path))),
      fields.zipWithIndex.map { (f, i) =>
        val spec = c.spec(c.stateOfType(cls.typeRef.memberType(f), cls.tree), cls.tree)
        RocqType.Field[Any, Any](StructureType.selector[Any, Any]((f.name, i), (name, names), spec.ty), spec)
      })

  /** The fields of a class that hold structures, each with its structure, in the order the constructor takes
    * them.
    */
  private def holding(c: Compiler)(cls: c.q.reflect.Symbol): List[(c.q.reflect.Symbol, c.q.reflect.Symbol)] =
    c.stateFields(cls).flatMap(f => c.declarableOf(cls.typeRef.memberType(f)).map(f -> _))

  /** Refused unless `words` are one for each structure the class holds, each a word of its field's structure. */
  private def given_(c: Compiler)(cls: c.q.reflect.Symbol, held: List[(String, String)],
      words: List[StructureDeclaration[?]]): Unit =
    val asked = s"`lifted[${cls.name}](${held.map(_._1).mkString(", ")})`"
    if held.size != words.size then throw NotRead(s"FrFlow: ${cls.name} holds ${held.size} structures and is " +
      s"given ${words.size} words: give the word of each, in order ($asked)")
    held.zip(words).foreach { case ((field, structure), w) =>
      if w.rocqType.ty != Ty.Data(TypeName(structure)) then throw NotRead(s"FrFlow: ${cls.name} holds $field, a " +
        s"$structure, and is given ${w.name.value}, which is no word of that structure ($asked)")
    }

  /** The structure a class implements. */
  private def implemented(c: Compiler)(cls: c.q.reflect.Symbol): c.q.reflect.Symbol =
    c.declarableOf(cls.typeRef).filter(_ != cls).getOrElse(throw NotRead(s"FrFlow: ${cls.name} implements no " +
      "structure: a trait of the developer's whose members are over domain types"))

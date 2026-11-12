package frflow.proof.rocq.threads

import frflow.core.threads.{Ctor, Decl, Program, Ty}

/** The Rocq file that states a generated file (`RocqThreads.file`, the module `gen`) agrees with one written by
  * hand of the same unit (the module `code`):
  *
  *   - each type of the generated file has the constructors of the hand-written type of its name, over the same
  *     arguments: a function from each to the other, constructor by constructor, which Rocq checks;
  *   - the generated definitions, read again over the hand-written file's types (`Module Over`: the text of the
  *     generated file's definitions, word for word), are each equal to the hand-written definition of its name by
  *     computation alone (`reflexivity`).
  *
  * `reordered` names the definitions whose parameters the hand-written file takes in another order, each with
  * that order: such a definition is equal to the hand-written one once its parameters are taken in it.
  */
object RocqAgreement:
  def file(p: Program, code: String, gen: String, reordered: Map[String, List[String]]): String =
    val own = types(p).map(_._1).toSet
    val lemmas = p.definitions.map(d => lemma(d.name, reordered.get(d.name).map(order =>
      s"(fun ${order.mkString(" ")} => @Over.${d.name} ${d.params.map(_.name).mkString(" ")})"), code)) :+
      lemma("interp", None, code)
    List(s"(** That `$gen`, generated, and `$code`, written by hand, agree: see `RocqAgreement`. Generated. *)",
      RocqThreads.imports.replace("Import ListNotations.",
        s"Require Import $code.\nRequire $gen.\nImport ListNotations."),
      "(** ** The types: each constructor takes the same arguments in both *)",
      (types(p).map(conversion(_, Way(gen, code, "to_code", own))) ++
        types(p).map(conversion(_, Way(code, gen, "of_code", own)))).mkString("\n\n"),
      "(** ** The generated definitions, over the hand-written file's types *)",
      over(p),
      "(** ** Each is the hand-written definition of its name *)",
      lemmas.mkString("\n")).mkString("\n\n") + "\n"

  /** The definitions of the generated file, in a module of their own: those among its types, then the others. */
  private def over(p: Program): String =
    val projections = p.types.collect { case d: Decl.Definition => PrintDecl(d)(using PrintTerm.Bars.Leading) }
    (List("Module Over.") ++ projections ++ List(RocqThreads.definitions(p), RocqThreads.interp(p, ""), "End Over."))
      .mkString("\n\n")

  /** That the generated definition `name` (`as`: with its parameters taken in the other file's order) is the
    * hand-written one.
    */
  private def lemma(name: String, as: Option[String], code: String): String =
    s"Lemma ${name}_agrees : ${as.getOrElse(s"@Over.$name")} = @$code.$name. Proof. reflexivity. Qed."

  /** The inductive types of the file, `code` among them, each as its name and constructors. */
  private def types(p: Program): List[(String, List[Ctor])] = p.types.collect {
    case Decl.Record(name, fields)   => name -> List(Ctor(Decl.maker(name), fields))
    case Decl.Inductive(name, ctors) => name -> ctors } :+ ("code" -> (p.closures :+ RocqThreads.client(p)))

  /** One way between the two files: from the module `from` to the module `to`, by functions named `name_<type>`
    * over the types `own` the files declare.
    */
  private final case class Way(from: String, to: String, name: String, own: Set[String])

  /** The function from the type `ty` of one module to that of the other, a constructor to its namesake. */
  private def conversion(ty: (String, List[Ctor]), way: Way): String =
    val (of, ctors) = ty
    val recursive = ctors.exists(_.params.exists(_.ty.names.contains(of)))
    val arms = ctors.map { c =>
      val args = c.params.indices.map(i => s"a${i + 1}").toList
      val made = args.zip(c.params).map((a, p) => converted(a, p.ty, way))
      s"  | ${way.from}.${(c.name :: args).mkString(" ")} => ${(s"${way.to}.${c.name}" :: made).mkString(" ")}" }
    s"${if recursive then "Fixpoint" else "Definition"} ${way.name}_$of (x : ${way.from}.$of) : ${way.to}.$of :=\n" +
      "  match x with\n" + arms.mkString("\n") + "\n  end."

  private def converted(arg: String, ty: Ty, way: Way): String = ty match
    case Ty.Named(n) if way.own(n)                      => s"(${way.name}_$n $arg)"
    case Ty.Of("option", of) if of.names.exists(way.own) =>
      s"(match $arg with Some y => Some ${converted("y", of, way)} | None => None end)"
    case Ty.Of("list", of) if of.names.exists(way.own)  => s"(List.map (fun y => ${converted("y", of, way)}) $arg)"
    case _                                              => arg

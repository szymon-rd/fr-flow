package frflow.core.threads

/** A declaration of the Rocq file a unit of code is read into. */
enum Decl:
  /** A class as the record of its fields: `Record C := mkC { C_f : T; … }.` */
  case Record(name: String, fields: List[Param])
  /** A sum, or a class with a field of its own type: `Inductive T := | A (x : X) | B.` */
  case Inductive(name: String, ctors: List[Ctor])
  /** `Definition name params : result := body.` */
  case Definition(name: String, params: List[Param], result: Ty, body: Term)

  def name: String

object Decl:
  /** The constructor of the record a class is. */
  def maker(record: String): String = s"mk$record"
  /** What reads a field of a class. */
  def projection(record: String, field: String): String = s"${record}_$field"

  /** The type of a program giving an `A`. */
  def M(of: Ty): Ty = Ty.Of("M", of)

  /** What a definition mentions: its body's names but its parameters, and its types' names. */
  def mentions(d: Definition): List[String] =
    (d.body.mentions.filterNot(d.params.map(_.name).contains) ++ d.params.flatMap(_.ty.names) ++ d.result.names)
      .distinct

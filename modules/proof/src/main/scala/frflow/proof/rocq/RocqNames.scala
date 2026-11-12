package frflow.proof.rocq

/** The names of a generated project as Rocq has them. The lowering names a constant as Lean reads it: by a path
  * through namespaces, read from the namespace it is written in outwards. Rocq has one flat scope of names here, so
  * a declared constant is its whole path joined (`commitMovesPast_Obl_impl`), without the model's name at its
  * head; a name FrFlow's support library gives (`List.foldl`) is the library's (`List_foldl`); a variable keeps
  * its name, unless Rocq or the library reads it as something else.
  */
final class RocqNames(declared: Set[List[String]]):
  /** The constant `path` names where it is written: in the namespace `in`, or one it is inside, or one opened. */
  def constant(path: List[String])(using c: RocqNames.Scope): String =
    (c.namespace.inits.toList ++ c.opens).map(_ ++ path).find(declared).map(RocqNames.joined)
      .orElse(RocqNames.library.get(path.mkString("."))).getOrElse(
        // a constant of the model's that no generated module declares: a proof file's (`Kb.node.Proofs.impl`)
        if path.sizeIs > 1 && c.namespace.headOption.contains(path.head) then RocqNames.joined(path)
        else path.map(RocqNames.identifier).mkString("_"))

  /** A name alone: a variable in scope, else a constant. */
  def name(n: String)(using c: RocqNames.Scope): String =
    if c.bound(n) then RocqNames.variable(n) else constant(List(n))

  def declaring(path: List[String]): String = RocqNames.joined(path)

object RocqNames:
  /** Where a term is written: its namespace, the namespaces opened there, and the variables bound around it. */
  final case class Scope(namespace: List[String], opens: List[List[String]], bound: Set[String]):
    def binding(names: Iterable[String]): Scope = copy(bound = bound ++ names)
    def inside(more: List[String]): Scope = copy(namespace = namespace ++ more)

  def of(paths: Iterable[List[String]]): RocqNames = RocqNames(paths.toSet)

  /** A declared constant's name: its path joined, the model's name at its head left out. */
  def joined(path: List[String]): String =
    (if path.sizeIs > 1 then path.drop(1) else path).map(identifier).mkString("_")

  /** A constructor of a type of the model (`Account_OfCard`, a record's `Decision_mk`). */
  def constructor(data: String, ctor: String): String = s"${identifier(data)}_${identifier(ctor)}"

  /** What reads a record's field, and what replaces it: one of each for a field's name, whatever the record. */
  def field(f: String): String = s"${identifier(f)}_of"
  def replacing(f: String): String = s"with_${identifier(f)}"

  /** A variable: its name, with `_` after it where Rocq or what the printer writes around it reads the name. */
  def variable(n: String): String =
    val id = identifier(n)
    if reserved(id) then id + "_" else id

  /** A Lean identifier as a Rocq one: its escape (`«by»`) taken off, a character Rocq has not made `_`. */
  def identifier(n: String): String =
    val plain = n.filterNot(c => c == '«' || c == '»').map(c => if c.isLetterOrDigit || c == '_' || c == '\'' then c
      else '_')
    if keywords(plain) then plain + "_" else plain

  private val keywords: Set[String] = Set("as", "at", "cofix", "else", "end", "exists", "exists2", "fix", "for",
    "forall", "fun", "if", "IF", "in", "let", "match", "mod", "Prop", "return", "Set", "then", "Type", "using",
    "where", "with", "by", "Definition", "Lemma", "Theorem", "Proof", "Qed")

  private val reserved: Set[String] = Set("fst", "snd", "In", "length", "ite", "decide", "Some", "None", "tt",
    "list", "option", "unit", "Z", "nat", "bool", "string", "True", "False", "I", "not", "and", "or", "eq", "pair",
    "nil", "cons", "app", "map", "filter", "sum", "prod", "id", "max", "min", "plus", "mult")

  /** What Lean's prelude and FrFlow's library call a thing, as Rocq's and the Rocq library do. */
  private val library: Map[String, String] = Map("True" -> "True", "False" -> "False", "Unit" -> "unit",
    "()" -> "tt", "Int" -> "Z", "Nat" -> "nat", "String" -> "string", "Prop" -> "Prop", "Type" -> "Type",
    "List" -> "list", "Option" -> "option", "some" -> "Some", "none" -> "None", "decide" -> "decide",
    "List.find?" -> "List_find")

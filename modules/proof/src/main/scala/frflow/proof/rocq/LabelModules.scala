package frflow.proof.rocq

import frflow.core.expr.{Expr, Exprs, Value}
import frflow.proof.layout.Lowering
import frflow.proof.prover.ast.*

/** The names of what a model's statements call by a label: a definition as an execution names it (`owner name
  * signature`), and a field of an object (`owner name`). A module `L` of abbreviations, one for each such text of
  * the statements, so that a proof names a method or a field (`L.ThreadHerd_threads`) and does not paste its label.
  * An abbreviation is the text itself to Rocq: a statement and a proof that names it read the same.
  */
object LabelModules:
  def of(l: Lowering): Option[ProverModule] =
    val t = l.resolved.theory
    val said = t.nodes.flatMap(_.node.statement.said).map(_.value) ++ t.vocabulary.defines.map(_.lambda.body)
    val texts = said.flatMap(Exprs.all).collect { case Expr.Lit(Value.Str(s), _) => s }
    Option(named(texts)).filter(_.nonEmpty).map(ns =>
      ProverModule(l.layout.labels, Nil, Preamble.generated, Names.path(l.kb.value), Nil, List(Decl.Rocq(text(ns)))))

  /** A text that names a definition or a field: two or three words, the first a class's or an object's full name,
    * the second a name a proof can write (a constructor's, or letters and digits: no operator), the third a
    * signature.
    */
  def isLabel(s: String): Boolean = s.split(" ", -1).toList match
    case List(owner, name)            => owner.contains('.') && written(name)
    case List(owner, name, signature) => owner.contains('.') && written(name) && signature.contains(':')
    case _                            => false

  private def written(name: String): Boolean =
    name == "<init>" || (name.nonEmpty && name.forall(c => c.isLetterOrDigit || c == '_'))

  /** Each label among the texts with its name, by name: its class's last name and its own (`KeySetView_add`; a
    * constructor is `new`), with how many things it takes where two would share a name, then a number.
    */
  def named(texts: List[String]): List[(String, String)] =
    val labels = texts.filter(isLabel).distinct.sorted
    val byArity = apart(labels.map(l => base(l) -> l))(l => s"_${taking(l)}")
    apart(byArity)(l => s"_${byArity.filter(_._1 == byArity.find(_._2 == l).get._1).map(_._2).indexOf(l) + 1}")
      .sortBy(_._1)

  /** Names shared by two labels told apart by what `more` adds to each. */
  private def apart(named: List[(String, String)])(more: String => String): List[(String, String)] =
    val shared = named.groupBy(_._1).filter(_._2.size > 1).keySet
    named.map((n, l) => (if shared(n) then n + more(l) else n) -> l)

  private def base(label: String): String =
    val owner :: name :: _ = label.split(" ", -1).toList: @unchecked
    val cls = owner.split('.').last.stripSuffix("$").replace("$package", "")
    ident(s"${cls}_${if name == "<init>" then "new" else name}")

  private def ident(s: String): String = s.map(c => if c.isLetterOrDigit || c == '_' then c else '_')

  /** How many things a definition takes, by its signature: none of a field. */
  private def taking(label: String): Int = label.split(" ", -1).lift(2).fold(0)(
    _.takeWhile(_ != ':').split(',').count(p => p.nonEmpty && !p.forall(_.isDigit)))

  private def text(named: List[(String, String)]): String =
    s"""From Stdlib Require Import String.
       |
       |(** What the model's statements call by a label, each by a name: a definition as an execution names it
       |    (its owner, its name, its signature) and a field of an object (its class, its name). *)
       |Module L.
       |${named.map((n, l) => s"  Abbreviation $n := \"$l\"%string.").mkString("\n")}
       |End L.""".stripMargin

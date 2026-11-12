package frflow.proof.reading

import frflow.proof.rocq.RocqNames

/** What Rocq said of one file it ran on (`file`, relative to the project's `rocq/`): its source and the report of
  * the build (`RocqReport`), read once; the report's other files are left out. `namespace` is the module's, as the
  * layout names it: a lemma `complete` of `Auth.accessExactly.Auto` is `accessExactly_Auto_complete` in Rocq, and
  * states `accessExactly_Obl_complete`.
  */
final case class Elaboration(source: String, output: String, file: String, namespace: List[String]):
  lazy val theorems: List[Theorem] = RocqSource.lemmas(source)
  private lazy val said: Option[RocqReport.File] = RocqReport.read(output).find(_.path == file)

  /** A lemma's name in Rocq, by its name in its module. */
  def named(name: String): String = RocqNames.joined(namespace :+ name)
  /** What a lemma proving the obligation `name` states: the obligation, declared in the node's `Spec`. */
  def obligation(name: String): String = RocqNames.joined(namespace.take(2) ++ List("Obl", name))
  def stated(name: String): Option[Theorem] = theorems.find(_.name == named(name))

  lazy val diagnostics: List[Diagnostic] = said.toList.flatMap(f =>
    f.broken.map(Diagnostic(file, 0, true, _)).toList ++ f.open.toList.sortBy(_._1).map((l, m) =>
      Diagnostic(file, theorems.find(_.name == l).fold(0)(_.from), true, m)))

  /** The axioms a lemma this file audits rests on (`Print Assumptions`), by its name in its module: the module's
    * own lemma, or the developer's proof of that obligation, which a module audits in its place.
    */
  def axiomsOf(name: String): Option[List[String]] = said.flatMap(f => f.assumes.get(named(name)).orElse(
    f.assumes.get(RocqNames.joined(namespace.take(2) ++ List("Proofs", name)))))

  def verdict(name: String): TheoremVerdict = (said, stated(name)) match
    case (Some(f), Some(t)) => f.broken.map(m => List(Diagnostic(file, 0, true, m)))
        .orElse(f.open.get(t.name).map(m => List(Diagnostic(file, t.from, true, m))))
        .fold(TheoremVerdict.Proven)(TheoremVerdict.Failed(_))
    case _                  => TheoremVerdict.Missing

package frflow.cli.text

import frflow.api.view.{Decided, Found, Listed, Rebased, Scaffolded, View}
import frflow.cli.say.Unprovens
import frflow.cli.term.Style

/** The short reports: where a change belongs (`find`), what a decision records, what `scaffold`, `rebase` and listing
  * the first decider wrote.
  */
object ReportText:
  /** The nodes governing a path, then those whose words mention the query, each in one line. */
  def found(query: String, f: Found, v: View, st: Style): List[String] =
    if f.governing.isEmpty && f.mentioning.isEmpty then
      Lines.para(s"Nothing governs or mentions \"$query\": a new concern may need a new node (and a governed home " +
        "for its code); a path is relative to the project's directory.", st, indent = 0)
    else Lines.section("Governed by", f.governing.map(Lines.of(v, _, st, 2)), st).drop(1) ++
      Lines.section("What mentions it", f.mentioning.map(Lines.of(v, _, st, 2)), st)
        .drop(if f.governing.isEmpty then 1 else 0)

  def decided(d: Decided, st: Style): List[String] = d.recorded.map((id, x) =>
    s"  ${st.bullet} ${Unprovens.verb(x.action)} $id" +
      (if x.reason.rejected.isEmpty then "" else s", rejecting ${x.reason.rejected.mkString(", ")}"))

  def scaffolded(s: Scaffolded): String = s match
    case Scaffolded.Written(file)     => s"wrote $file: a stub for each obligation left open (replace each sorry)"
    case Scaffolded.NothingToAdd => "nothing to stub: the proof file already has a theorem for each open obligation"
    case Scaffolded.EndNotFound(file) => s"$file has no closing `end` of its namespace: no stubs added"

  def rebased(r: Rebased): List[String] = List(
    s"wrote ${r.file}: the ledger as it reads now (sha256 ${r.ledger.take(16)}…) is where its committed history starts",
    "commit it with .frflow/ledger.json: it counts once committed")

  def listed(l: Listed): String = l match
    case Listed.Written(file) =>
      s"wrote $file, listing you as the first decider: commit it (only committed lists count)"
    case Listed.Already(file) => s"$file is there already: a later version is signed by a key it lists"

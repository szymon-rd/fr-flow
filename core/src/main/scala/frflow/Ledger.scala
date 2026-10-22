package frflow

import frflow.Json.*
import java.nio.charset.StandardCharsets.UTF_8
import java.nio.file.{Files, Path}

/** Result of one obligation: `proven`, `open` or `failed`. A try (a statement Lean is asked whether it
  * can prove, see `Generate.tries`) has a plain status instead, saying what Lean shows: `needed` or
  * `not-needed` (a part, and `vacuous` with one part), `no-clash` or `clash`, `not-unsat` or `unsat`,
  * `not-idle` or `idle`, `not-vacuous` or `vacuous` (an expectation).
  */
final case class Result(name: String, status: String, detail: String = ""):
  /** A limit of what the node says, not an obligation: `idle` means doing nothing meets the root. */
  def isLimit: Boolean = name == "idle"
  /** Lean evaluating an example as Scala does: the translation's cross-check. */
  def isEvaluation: Boolean = name.startsWith("eval") || name.startsWith("probe")
  /** Nothing to do about it: an obligation proven, a try that shows nothing wrong, or a limit. */
  def fine: Boolean = isLimit || Result.Fine(status)

object Result:
  /** The statuses that leave nothing to do: an obligation proven, a try showing nothing wrong. */
  val Fine: Set[String] = Set("proven", "needed", "no-clash", "not-unsat", "not-idle", "not-vacuous")


/** The outcome of checking one node. `status` is `proven`, `open`, `failed`,
  * `model-error` or `waiting` (proven, but its parent is not yet).
  */
final case class NodeCheck(
    hash: String,
    status: String,
    obligations: List[Result],
    messages: List[String],
    axioms: List[String],
    at: String
)

/** A decision of the developer about a node.
  *
  * @param action   `accept` (the developer chose the node, as seen), `confirm`
  *                 (it still holds after something above it moved), `reject` (an alternative not
  *                 chosen, as it was proposed), `revisit` (the developer said a change above may affect
  *                 it, so it is reviewed again), `remove` (the developer agreed that a decided node is
  *                 gone), or `migrate` (recorded by an earlier FrFlow when its format changed)
  * @param content  the node as the developer saw it; the decision is bound to its hash
  * @param chain    the content of the ancestors, as decided; when it changes, the node is reviewed
  * @param reason   why: kept as part of the theory
  * @param rejected for `accept`, the alternatives rejected by this choice
  * @param code     the fingerprint of the source files the node governs, when decided
  * @param held     the decisions below that were shown with this one and left as they are:
  *                 considered, and still holding
  * @param after    the node's decision this one follows (its `ref`): two decisions following the same
  *                 one come from two branches, merged; the node is then decided again
  * @param from     for an `accept` that renames a gone node: its old id, whose history it continues
  * @param commit   the git commit checked out when deciding
  * @param tree     the code as decided, written to git as a tree, to show how the code changed since
  *                 (a clone without it falls back to `commit`)
  */
final case class Decision(action: String, content: Json, chain: String, by: String, at: String, reason: String,
    rejected: List[String] = Nil, code: String = "", commit: String = "", tree: String = "", held: List[String] = Nil,
    after: String = "", key: String = "", sig: String = "", from: String = ""):
  def hash: String = Decision.hash(content)
  /** The decision without its signature: what is signed, and what a rewrite is judged on. */
  def unsigned: Decision = copy(key = "", sig = "")

object Decision:
  /** The hash a decision is bound to. Runs of whitespace count as one space, so reformatting
    * changes nothing that was decided.
    */
  def hash(content: Json): String =
    Sha(normal(content).compact)

  private def normal(j: Json): Json = j match
    case JStr(s)  => JStr(s.trim.replaceAll("\\s+", " "))
    case JArr(xs) => JArr(xs.map(normal))
    case JObj(fs) => JObj(fs.map((k, v) => k -> normal(v)))
    case other    => other

/** The developer's decisions, per node, oldest first: the record of the theory and its history.
  * Kept in `.frflow/ledger.json` and committed. Nothing in it is ever overwritten.
  */
final case class Ledger(decisions: Map[String, List[Decision]]):
  /** A node's decisions; a renamed node's start with those of the id it had. */
  def history(id: String): List[Decision] = history(id, Set.empty)
  private def history(id: String, seen: Set[String]): List[Decision] =
    val own = decisions.getOrElse(id, Nil)
    own.headOption.map(_.from).filter(f => f.nonEmpty && !seen(f) && f != id).fold(own)(f => history(f, seen + id) ++ own)
  /** Renames: each old id, with the id it has now. */
  lazy val renames: Map[String, String] =
    decisions.toList.flatMap((id, ds) => ds.headOption.map(_.from).filter(_.nonEmpty).map(_ -> id)).toMap
  def current(id: String): Option[Decision] = history(id).lastOption
  /** The developer's choice of the node: the acceptance that chose it (the first since it was last
    * rejected or removed), which carries the reason it was chosen. Later acceptances are of changes.
    */
  def chosen(id: String): Option[Decision] =
    history(id).reverse.takeWhile(d => d.action != "reject" && d.action != "remove").reverse
      .find(_.action == "accept")
  /** The decisions since the node was chosen: its choice, the changes accepted and confirmations. */
  def sinceChosen(id: String): List[Decision] =
    history(id).reverse.takeWhile(d => d.action != "reject" && d.action != "remove").reverse.dropWhile(_.action != "accept")

  /** What the node is bound to now: its last acceptance or confirmation (also while the developer
    * has asked to revisit it).
    */
  def binding(id: String): Option[Decision] = current(id) match
    case Some(d) if d.action == "revisit" => history(id).reverse.find(x => Ledger.binds(x.action))
    case c => c.filter(d => Ledger.binds(d.action))

  def add(id: String, d: Decision): Ledger =
    Ledger(decisions.updated(id, decisions.getOrElse(id, Nil) :+ d.copy(after = current(id).fold("")(Ledger.entry))))

  /** Two branches decided the node, and the merge kept both: the last decision is one of two that
    * follow the same one, or follows none (a first decision) though others come before it. Nothing
    * says which holds, so the node is decided again.
    */
  def forked(id: String): Boolean =
    current(id).exists(d => if d.after.isEmpty then decisions.getOrElse(id, Nil).size > 1 else history(id).count(_.after == d.after) > 1)

  /** The alternatives ever rejected in favour of a node, as they were proposed. */
  def alternatives(id: String): List[(String, Json)] =
    history(id).filter(_.action == "accept").flatMap(_.rejected).distinct
      .flatMap(r => history(r).reverse.find(_.action == "reject").map(d => r -> d.content))

  /** The nodes rejected under `parent` (now or once), each with its content and the reason: the
    * options already turned down where a new proposal stands.
    */
  def rejectedUnder(parent: String): List[(String, Json, String)] =
    decisions.toList.sortBy(_._1).flatMap((id, ds) => ds.lastOption.filter(d => d.action == "reject" &&
      (d.content("parent").flatMap(_.str).contains(parent) || d.content("parents").exists(_.arr.flatMap(_.str).contains(parent)))).map(d => (id, d.content, d.reason)))

  /** Every decision, newest first. */
  def all: List[(String, Decision)] = decisions.toList.flatMap((id, ds) => ds.map(id -> _)).sortBy(_._2.at).reverse

  /** Content already recorded for the node is written once, then referred to by its hash
    * ("content": "same:<hash>"), which stays right when a merge interleaves two branches' decisions.
    */
  def toJson: Json =
    obj("decisions" -> JObj(decisions.toSeq.sortBy(_._1).map { (id, ds) =>
      id -> JArr(ds.zipWithIndex.map((d, i) => JObj(Seq(
        "action" -> str(d.action), "by" -> str(d.by), "at" -> str(d.at), "reason" -> str(d.reason)) ++
        (if d.rejected.isEmpty then Nil else Seq("rejected" -> JArr(d.rejected.map(str)))) ++
        (if d.held.isEmpty then Nil else Seq("held" -> JArr(d.held.map(str)))) ++
        (if d.after.isEmpty then Nil else Seq("after" -> str(d.after))) ++
        (if d.from.isEmpty then Nil else Seq("from" -> str(d.from))) ++
        (if d.code.isEmpty then Nil else Seq("code" -> str(d.code))) ++
        (if d.commit.isEmpty then Nil else Seq("commit" -> str(d.commit))) ++
        (if d.tree.isEmpty then Nil else Seq("tree" -> str(d.tree))) ++
        (if d.sig.isEmpty then Nil else Seq("key" -> str(d.key), "sig" -> str(d.sig))) ++
        Seq("chain" -> str(d.chain), "content" -> (if ds.take(i).exists(_.content == d.content) then str("same:" + Ledger.ref(d.content)) else d.content)))))
    }))

object Ledger:
  val empty: Ledger = Ledger(Map.empty)

  /** Two branches' ledgers merged: every decision of either, each node's in order (this side's,
    * then the other's that this one lacks). A node both sides decided is `forked`, and decided
    * again. Git's merge driver for the ledger.
    */
  def merge(ours: Ledger, theirs: Ledger): Ledger =
    Ledger((ours.decisions.keySet ++ theirs.decisions.keySet).toList.map { id =>
      val mine = ours.history(id)
      val seen = mine.map(entry).toSet
      id -> (mine ++ theirs.history(id).filterNot(d => seen(entry(d))))
    }.toMap)

  /** Actions a node is bound to: the developer's acceptance or confirmation, or a migration. */
  def binds(action: String): Boolean = Set("accept", "confirm", "migrate")(action)

  /** A short reference to a decision: what was decided, by whom, when and why. */
  private[frflow] def entry(d: Decision): String =
    Sha.parts(d.action, d.by, d.at, d.reason, ref(d.content)).take(16)

  /** A short reference to a content exactly as recorded. */
  private[frflow] def ref(content: Json): String =
    Sha(content.compact).take(16)

  /** The decisions of `before` that `now` lost: the ledger only grows, so each is a merge gone wrong
    * (a text merge, a conflict resolved by hand) or an edit.
    */
  def lost(before: Ledger, now: Ledger): List[(String, Decision)] =
    val kept = now.decisions.values.flatten.map(entry).toSet
    before.decisions.toList.sortBy(_._1).flatMap((id, ds) => ds.filterNot(d => kept(entry(d))).map(id -> _))

  def load(file: Path): Ledger =
    if !Files.isRegularFile(file) then empty else fromJson(Json.parse(Files.readString(file, UTF_8)))

  /** Written whole, then moved into place: a reader (the browser polls it) never sees half a ledger. */
  def save(file: Path, l: Ledger): Unit =
    val dir = file.toAbsolutePath.getParent
    Files.createDirectories(dir)
    val tmp = Files.createTempFile(dir, ".ledger", ".tmp")
    Files.writeString(tmp, l.toJson.render() + "\n", UTF_8)
    Files.move(tmp, file, java.nio.file.StandardCopyOption.REPLACE_EXISTING, java.nio.file.StandardCopyOption.ATOMIC_MOVE)

  import Json.text as s

  def fromJson(j: Json): Ledger =
    Ledger(j("decisions").map(_.obj).getOrElse(Nil).map { (id, ds) =>
      id -> ds.arr.foldLeft(List.empty[Decision]) { (acc, d) =>
        val content = d("content") match
          case Some(JStr("same")) => acc.lastOption.fold(JNull)(_.content) // the earlier form: the previous entry's
          case Some(JStr(ref)) if ref.startsWith("same:") =>
            acc.reverse.find(x => Ledger.ref(x.content) == ref.stripPrefix("same:")).fold(JNull)(_.content)
          case other => other.getOrElse(JNull)
        acc :+ Decision(s(d, "action"), content, s(d, "chain"), s(d, "by"), s(d, "at"), s(d, "reason"),
          d("rejected").map(_.arr).getOrElse(Nil).flatMap(_.str).toList, s(d, "code"), s(d, "commit"), s(d, "tree"),
          d("held").map(_.arr).getOrElse(Nil).flatMap(_.str).toList, s(d, "after"), s(d, "key"), s(d, "sig"), s(d, "from"))
      }
    }.toMap)

  /** What `status` and the browser warn about the record itself: decisions not signed by a key in
    * `.frflow/keys` (the developer's: the browser creates it and signs with it).
    */
  def warnings(file: Path, now: Ledger): List[String] =
    val keys = file.getParent.resolve("keys")
    (if now.decisions.nonEmpty && Signing.keys(keys).isEmpty then
      List("no developer key: start the browser (`frflow serve`), which creates your key, and commit .frflow/keys/") else Nil) ++
    Signing.unsigned(now, keys).map((id, d) =>
      s"$id: the ${d.action} of ${d.at} by ${d.by} is not signed by a developer key: decide it again in the browser, or sign it there if it is yours") ++
    Signing.misnamed(now, keys).map((id, d, name) =>
      s"$id: the ${d.action} of ${d.at} says ${d.by} decided it, but it is signed with $name's key")

/** Check results, derived from the model and Lean; kept in `.frflow/checks.json`, not committed. */
object Checks:
  import Json.text as s
  private def strs(j: Option[Json]) = j.map(_.arr).getOrElse(Nil).flatMap(_.str).toList

  def load(file: Path): Map[String, NodeCheck] =
    if !Files.isRegularFile(file) then Map.empty
    else Json.parse(Files.readString(file, UTF_8)).obj.map { (id, c) =>
      id -> NodeCheck(s(c, "hash"), s(c, "status"),
        c("obligations").map(_.arr).getOrElse(Nil).map(r => Result(s(r, "name"), s(r, "status"), s(r, "detail"))).toList,
        strs(c("messages")), strs(c("axioms")), s(c, "at"))
    }.toMap

  def save(file: Path, checks: Map[String, NodeCheck]): Unit =
    Files.createDirectories(file.getParent)
    Files.writeString(file, JObj(checks.toSeq.sortBy(_._1).map { (id, c) =>
      id -> obj("hash" -> str(c.hash), "status" -> str(c.status), "at" -> str(c.at),
        "obligations" -> JArr(c.obligations.map(r => obj("name" -> str(r.name), "status" -> str(r.status), "detail" -> str(r.detail)))),
        "messages" -> JArr(c.messages.map(str)), "axioms" -> JArr(c.axioms.map(str)))
    }).render() + "\n", UTF_8)

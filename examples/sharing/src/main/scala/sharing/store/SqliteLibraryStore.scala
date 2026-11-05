package sharing.store

import cats.effect.IO
import java.sql.{Connection, DriverManager, ResultSet}
import sharing.domain.*

/** The library in SQLite, as today's (`SqlLibraryStore`): one table per kind of row, each row with its place in its
  * list (`pos`), so the library is read back in the order it was saved. Times (seconds) are kept as text, exactly; none
  * is null. A log entry and a notice are kept whole, each in a row of its own (serialized). A save replaces every row
  * in one transaction: a save that fails changes nothing. Tested against `libraryModel` beside the store in memory.
  * One connection, its calls one at a time.
  */
final class SqliteLibraryStore private (conn: Connection):
  private val tables = List(
    "documents (pos integer primary key, id text not null, title text not null, trashed text, owner text not null)",
    "document_folders (doc integer not null, pos integer not null, folder text not null, primary key (doc, pos))",
    "folders (pos integer primary key, id text not null, name text not null)",
    "folder_folders (folder integer not null, pos integer not null, around text not null, primary key (folder, pos))",
    "teams (pos integer primary key, id text not null)",
    "members (team integer not null, pos integer not null, person text not null, primary key (team, pos))",
    "shares (pos integer primary key, what text not null, what_id text not null, with_whom text not null, " +
      "with_id text not null, level text not null, until text)",
    "invitations (pos integer primary key, to_person text not null, what text not null, what_id text not null, " +
      "level text not null, by_person text not null, sent text not null)",
    "requests (pos integer primary key, person text not null, what text not null, what_id text not null, " +
      "level text not null, asked text not null, reminded integer not null)",
    "log (pos integer primary key, entry text not null)",
    "outbox (pos integer primary key, notice text not null)")
  tables.foreach(t => conn.createStatement().executeUpdate(s"create table if not exists $t"))

  def load: IO[Library] = IO.blocking(library)
  def save(l: Library): IO[Unit] = IO.blocking(replaceWith(l))

  /** The library the rows make. */
  def library: Library = synchronized {
    val (docFolders, around, members) = (grouped("document_folders", "doc", "folder")(FolderId(_)),
      grouped("folder_folders", "folder", "around")(FolderId(_)), grouped("members", "team", "person")(PersonId(_)))
    Library(
      rows("select pos, id, title, trashed, owner from documents order by pos")(r =>
        Document(DocumentId(r.getString(2)), r.getString(3), docFolders.getOrElse(r.getInt(1), Nil), time(r, 4),
          PersonId(r.getString(5)))),
      rows("select pos, id, name from folders order by pos")(r =>
        Folder(FolderId(r.getString(2)), r.getString(3), around.getOrElse(r.getInt(1), Nil))),
      rows("select pos, id from teams order by pos")(r =>
        Team(TeamId(r.getString(2)), members.getOrElse(r.getInt(1), Nil))),
      rows("select what, what_id, with_whom, with_id, level, until from shares order by pos")(share),
      rows("select to_person, what, what_id, level, by_person, sent from invitations order by pos")(invitation),
      rows("select person, what, what_id, level, asked, reminded from requests order by pos")(request),
      rows("select entry from log order by pos")(r => whole[Entry](r.getString(1))),
      rows("select notice from outbox order by pos")(r => whole[Notice](r.getString(1))))
  }

  /** A list kept in rows of its own, by the place of what holds it. */
  private def grouped[A](table: String, of: String, value: String)(read: String => A): Map[Int, List[A]] =
    rows(s"select $of, $value from $table order by $of, pos")(r => r.getInt(1) -> read(r.getString(2)))
      .groupMap(_._1)(_._2)

  private def invitation(r: ResultSet): Invitation =
    Invitation(PersonId(r.getString(1)), target(r.getString(2), r.getString(3)), Level.valueOf(r.getString(4)),
      PersonId(r.getString(5)), BigInt(r.getString(6)))

  private def request(r: ResultSet): AccessRequest =
    AccessRequest(PersonId(r.getString(1)), target(r.getString(2), r.getString(3)), Level.valueOf(r.getString(4)),
      BigInt(r.getString(5)), r.getInt(6) != 0)

  /** Every row replaced by the library's, in one transaction. */
  private def replaceWith(l: Library): Unit = synchronized {
    conn.setAutoCommit(false)
    try
      List("documents", "document_folders", "folders", "folder_folders", "teams", "members", "shares", "invitations",
        "requests", "log", "outbox").foreach(t => conn.createStatement().executeUpdate(s"delete from $t"))
      insertAll(l)
      conn.commit()
    catch
      case e: Throwable =>
        conn.rollback()
        throw e
    finally conn.setAutoCommit(true)
  }

  private def insertAll(l: Library): Unit =
    l.documents.zipWithIndex.foreach { (d, i) =>
      insert("documents", i, d.id.name, d.title, d.trashed.map(_.toString).orNull, d.owner.name)
      d.folders.zipWithIndex.foreach((f, j) => insert("document_folders", i, j, f.name))
    }
    l.folders.zipWithIndex.foreach { (f, i) =>
      insert("folders", i, f.id.name, f.name)
      f.folders.zipWithIndex.foreach((g, j) => insert("folder_folders", i, j, g.name))
    }
    l.teams.zipWithIndex.foreach { (t, i) =>
      insert("teams", i, t.id.name)
      t.members.zipWithIndex.foreach((p, j) => insert("members", i, j, p.name))
    }
    l.shares.zipWithIndex.foreach((s, i) => insert("shares", (i :: shareRow(s))*))
    insertKept(l)

  private def shareRow(s: Share): List[Any] =
    val (what, whatId) = targetRow(s.what)
    val (withWhom, withId) = s.withWhom match
      case Grantee.Person(p) => ("person", p.name)
      case Grantee.Team(t)   => ("team", t.name)
    List(what, whatId, withWhom, withId, s.level.toString, s.until.map(_.toString).orNull)

  private def insertKept(l: Library): Unit =
    l.invitations.zipWithIndex.foreach { (v, i) =>
      val (what, whatId) = targetRow(v.what)
      insert("invitations", i, v.to.name, what, whatId, v.level.toString, v.by.name, v.sent.toString)
    }
    l.requests.zipWithIndex.foreach { (q, i) =>
      val (what, whatId) = targetRow(q.what)
      insert("requests", i, q.person.name, what, whatId, q.level.toString, q.asked.toString,
        if q.reminded then 1 else 0)
    }
    l.log.zipWithIndex.foreach((e, i) => insert("log", i, kept(e)))
    l.outbox.zipWithIndex.foreach((n, i) => insert("outbox", i, kept(n)))

  /** A value kept whole in a row: serialized, as text. */
  private def kept(v: java.io.Serializable): String =
    val out = java.io.ByteArrayOutputStream()
    val o = java.io.ObjectOutputStream(out)
    o.writeObject(v)
    o.close()
    java.util.Base64.getEncoder.encodeToString(out.toByteArray)

  private def whole[T](s: String): T =
    java.io.ObjectInputStream(java.io.ByteArrayInputStream(java.util.Base64.getDecoder.decode(s))).readObject()
      .asInstanceOf[T]

  private def time(r: ResultSet, i: Int): Option[BigInt] = Option(r.getString(i)).map(BigInt(_))
  private def target(kind: String, id: String): Target =
    if kind == "doc" then Target.Doc(DocumentId(id)) else Target.InFolder(FolderId(id))
  private def targetRow(t: Target): (String, String) = t match
    case Target.Doc(d)      => ("doc", d.name)
    case Target.InFolder(f) => ("folder", f.name)

  private def share(r: ResultSet): Share =
    val withWhom = if r.getString(3) == "person" then Grantee.Person(PersonId(r.getString(4)))
      else Grantee.Team(TeamId(r.getString(4)))
    Share(target(r.getString(1), r.getString(2)), withWhom, Level.valueOf(r.getString(5)), time(r, 6))

  private def insert(table: String, values: Any*): Unit =
    val st = conn.prepareStatement(s"insert into $table values (${values.map(_ => "?").mkString(", ")})")
    values.zipWithIndex.foreach((v, i) => st.setObject(i + 1, v))
    st.executeUpdate(): Unit

  private def rows[T](sql: String)(read: ResultSet => T): List[T] =
    val rs = conn.createStatement().executeQuery(sql)
    val out = List.newBuilder[T]
    while rs.next() do out += read(rs)
    out.result()

object SqliteLibraryStore:
  /** A store in memory holding the library: for tests. */
  def holding(l: Library): IO[SqliteLibraryStore] = IO.blocking {
    val s = SqliteLibraryStore(DriverManager.getConnection("jdbc:sqlite::memory:"))
    s.replaceWith(l)
    s
  }

package sharing.http

import io.circe.{ACursor, Json}
import io.circe.parser.parse
import sharing.domain.*

/** Why a request is not one the service answers: no such route, or a route with input it cannot read. */
enum Invalid:
  case NoRoute(method: String, path: String)
  case Unreadable(reason: String)

/** HTTP to requests and answers to HTTP: plain code, tested (SharingSuite).
  *   GET  /access?person=bob&doc=q3-report                                                        → {"access":"view"}
  *   POST /share    {"by":"ann","what":{"doc":"plan"},"with":{"person":"bob"},"level":"view"}      → {"done":true}
  *   POST /unshare  {"by":"ann","what":{"folder":"reports"},"with":{"team":"eng"}}
  *   POST /move     {"by":"ann","doc":"plan","into":"reports"}  (no "into": out of every folder)
  * A refused change is 403; an unreadable request 400 with the reason; an unknown route 404.
  */
object HttpCodec:
  def request(method: String, path: String, query: Map[String, String], body: String): Either[Invalid, Request] =
    (method, path) match
      case ("GET", "/access") =>
        for
          p <- query.get("person").filter(_.nonEmpty).toRight(Invalid.Unreadable("person is missing"))
          d <- query.get("doc").filter(_.nonEmpty).toRight(Invalid.Unreadable("doc is missing"))
        yield Request.Access(PersonId(p), DocumentId(d))
      case ("POST", "/share") =>
        json(body).flatMap(j =>
          for by <- name(j, "by"); what <- target(j); withWhom <- grantee(j); level <- level(j)
          yield Request.Share(PersonId(by), what, withWhom, level))
      case ("POST", "/unshare") =>
        json(body).flatMap(j =>
          for by <- name(j, "by"); what <- target(j); withWhom <- grantee(j) yield Request.Unshare(PersonId(by), what, withWhom))
      case ("POST", "/move") =>
        json(body).flatMap(j =>
          for
            by   <- name(j, "by")
            doc  <- name(j, "doc")
            into <- j.downField("into").focus.filterNot(_.isNull).fold(Right(None))(f => f.asString.filter(_.nonEmpty)
              .toRight(Invalid.Unreadable("into is not a folder's id")).map(i => Some(FolderId(i))))
          yield Request.Move(PersonId(by), DocumentId(doc), into))
      case _ => Left(Invalid.NoRoute(method, path))

  /** The status and body an answer is sent with. */
  def reply(a: Answer): (Int, Json) = a match
    case Answer.Access(level) => 200 -> Json.obj("access" -> Json.fromString(level.fold("none")(_.toString.toLowerCase)))
    case Answer.Done          => 200 -> Json.obj("done" -> Json.True)
    case Answer.Refused       => 403 -> Json.obj("refused" -> Json.fromString("you may not edit it"))

  def reply(i: Invalid): (Int, Json) = i match
    case Invalid.NoRoute(m, p)  => 404 -> Json.obj("error" -> Json.fromString(s"no route $m $p"))
    case Invalid.Unreadable(why) => 400 -> Json.obj("error" -> Json.fromString(why))

  private def json(body: String): Either[Invalid, ACursor] =
    parse(body).left.map(_ => Invalid.Unreadable("the body is not JSON")).map(_.hcursor)

  private def name(j: ACursor, field: String): Either[Invalid, String] =
    j.downField(field).focus.flatMap(_.asString).filter(_.nonEmpty).toRight(Invalid.Unreadable(s"$field is missing"))

  private def target(j: ACursor): Either[Invalid, Target] =
    val w = j.downField("what")
    name(w, "doc").map(d => Target.Doc(DocumentId(d)))
      .orElse(name(w, "folder").map(f => Target.InFolder(FolderId(f))))
      .left.map(_ => Invalid.Unreadable("what is neither a doc nor a folder"))

  private def grantee(j: ACursor): Either[Invalid, Grantee] =
    val w = j.downField("with")
    name(w, "person").map(p => Grantee.Person(PersonId(p)))
      .orElse(name(w, "team").map(t => Grantee.Team(TeamId(t))))
      .left.map(_ => Invalid.Unreadable("with is neither a person nor a team"))

  private def level(j: ACursor): Either[Invalid, Level] =
    name(j, "level").flatMap {
      case "view" => Right(Level.View)
      case "edit" => Right(Level.Edit)
      case other  => Left(Invalid.Unreadable(s"level is view or edit, not $other"))
    }

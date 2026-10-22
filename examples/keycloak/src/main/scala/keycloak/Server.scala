package keycloak

import com.sun.net.httpserver.{HttpExchange, HttpServer}
import java.net.InetSocketAddress
import java.nio.charset.StandardCharsets.UTF_8
import java.security.SecureRandom
import java.util.Base64
import javax.crypto.SecretKeyFactory
import javax.crypto.spec.PBEKeySpec

/** Keycloak's OpenID Connect endpoints, for each realm. Every request reaches the sessions through
  * the wiring (`Realms`), which runs the proven core through `service`. HttpApi governs this file.
  *
  *   POST /realms/{realm}/protocol/openid-connect/token             grant_type=password&username=..&password=..
  *   POST /realms/{realm}/protocol/openid-connect/token/introspect  token=..
  *   POST /realms/{realm}/protocol/openid-connect/logout            token=..
  *   PUT  /admin/realms/{realm}/users/{username}                    {"enabled":false}   (an administrator)
  */
object AuthServer:
  private val random = SecureRandom()

  /** PBKDF2 of a password with a salt: what the core compares with the stored hash. */
  def hash(password: String, salt: String): String =
    val spec = PBEKeySpec(password.toCharArray, salt.getBytes(UTF_8), 100_000, 256)
    Base64.getEncoder.encodeToString(SecretKeyFactory.getInstance("PBKDF2WithHmacSHA256").generateSecret(spec).getEncoded)

  /** A fresh token: 256 random bits. */
  def freshToken(): String = Base64.getUrlEncoder.withoutPadding.encodeToString(Array.fill[Byte](32)(0).tap(random.nextBytes))

  extension [T](t: T) private def tap(f: T => Unit): T = { f(t); t }

  def start(realms: Realms, salts: Map[(RealmId, String), String], port: Int): HttpServer =
    val server = HttpServer.create(InetSocketAddress("127.0.0.1", port), 0)
    val Path = "/realms/([^/]+)/protocol/openid-connect/(token|token/introspect|logout)".r
    val Admin = "/admin/realms/([^/]+)/users/([^/]+)".r
    server.createContext("/", (ex: HttpExchange) =>
      try
        val body = String(ex.getRequestBody.readAllBytes(), UTF_8)
        val form = params(body)
        (ex.getRequestMethod, ex.getRequestURI.getPath) match
          case ("PUT", Admin(r, u)) =>
            val on = !body.replace(" ", "").contains("\"enabled\":false")
            if realms.setEnabled(RealmId(r), u, on) then reply(ex, 204, "") else reply(ex, 404, """{"error":"User not found"}""")
          case ("POST", Path(r, "token")) if form.get("grant_type").contains("password") =>
            val (realm, user) = (RealmId(r), form.getOrElse("username", ""))
            val salt = salts.getOrElse((realm, user), "no-such-user")
            val token = freshToken()
            val opened = realms.handle(AuthRequest.SignIn(realm, user, hash(form.getOrElse("password", ""), salt), token))
              .sessions.contains(Session(token, realm, user))
            if opened then reply(ex, 200, s"""{"access_token":${str(token)},"token_type":"Bearer"}""")
            else reply(ex, 401, """{"error":"invalid_grant","error_description":"Invalid user credentials"}""")
          case ("POST", Path(r, "token/introspect")) =>
            realms.introspect(RealmId(r), form.getOrElse("token", "")) match
              case Some(c) =>
                reply(ex, 200, s"""{"active":true,"iss":${str(s"http://127.0.0.1:$port/realms/${c.realm.name}")},"username":${str(c.user)},""" +
                  s""""realm_access":{"roles":${c.roles.map(str).mkString("[", ",", "]")}}}""")
              case None => reply(ex, 200, """{"active":false}""")
          case ("POST", Path(r, "logout")) =>
            realms.handle(AuthRequest.SignOut(RealmId(r), form.getOrElse("token", "")))
            reply(ex, 204, "")
          case _ => reply(ex, 404, """{"error":"not found"}""")
      catch
        case e: frflow.ContractViolation => reply(ex, 500, s"""{"error":${str(e.getMessage)}}""")
        case e: Exception => reply(ex, 400, s"""{"error":${str(String.valueOf(e.getMessage))}}""")
    )
    server.start()
    server

  private def params(body: String): Map[String, String] =
    body.split("&").toList.map(_.split("=", 2)).collect { case Array(k, v) =>
      java.net.URLDecoder.decode(k, UTF_8) -> java.net.URLDecoder.decode(v, UTF_8) }.toMap
  private def str(s: String) = "\"" + s.replace("\\", "\\\\").replace("\"", "\\\"") + "\""
  private def reply(ex: HttpExchange, code: Int, s: String) =
    val b = s.getBytes(UTF_8)
    ex.getResponseHeaders.add("Content-Type", "application/json")
    if code == 204 then ex.sendResponseHeaders(204, -1)
    else
      ex.sendResponseHeaders(code, b.length)
      ex.getResponseBody.write(b)
    ex.close()

/** The realms loaded at start (Not modelled: creating them): username, password, enabled, roles. */
private val realmsAtStart = List(
  ("acme", "alice", "wonderland", true, List("admin", "user")),
  ("acme", "bob", "builder", true, List("user")),
  ("globex", "carol", "secret", true, List("viewer")))

/** Serves the realms: `sbt "keycloak/runMain keycloak.serveRealms 8080"`. `serveRealms 8080 bob` loads
  * Bob disabled; an administrator enables or disables a user with the admin endpoint.
  */
@main def serveRealms(port: Int, disabled: String*): Unit =
  val salts = realmsAtStart.map((r, u, _, _, _) => (RealmId(r), u) -> s"$r/$u/salt").toMap
  val accounts = realmsAtStart.map((r, u, pw, on, roles) =>
    UserAccount(RealmId(r), u, AuthServer.hash(pw, salts((RealmId(r), u))), on && !disabled.contains(u), roles))
  AuthServer.start(Realms(accounts, SessionDb.loaded(accounts)), salts, port)
  println(s"Realms on http://127.0.0.1:$port: ${realmsAtStart.map(_._1).distinct.mkString(", ")}")

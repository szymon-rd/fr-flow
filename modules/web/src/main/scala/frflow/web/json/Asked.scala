package frflow.web.json

import cats.syntax.all.*
import frflow.core.name.NodeId
import frflow.decision.rules.Command
import io.circe.{Decoder, DecodingFailure, HCursor}

/** A decision as the page sends it: `{"action": "accept", "nodes": […], "revisit": […], "seen": {node: version}}`
  * and `confirm`, which take no reason; `reject` with its `node`, `reason` and the `seen` version; `revisit` and
  * `gone` with their `node` and `reason`.
  */
object Asked:
  private given Decoder[NodeId] = Decoder.decodeString.map(NodeId(_))

  given Decoder[Command] = Decoder.instance(c => c.get[String]("action").flatMap(command(c, _)))

  private def command(c: HCursor, action: String): Decoder.Result[Command] =
    val why = c.get[String]("reason")
    action match
      case "accept"  => (c.get[List[NodeId]]("nodes"), c.getOrElse[List[NodeId]]("revisit")(Nil),
          c.getOrElse[Map[String, String]]("seen")(Map.empty)).mapN((ns, r, seen) =>
          Command.Accept(ns, r, seen.map((k, v) => NodeId(k) -> v)))
      case "reject"  => (c.get[NodeId]("node"), why, c.get[Option[String]]("seen")).mapN(Command.Reject(_, _, _))
      case "confirm" => Right(Command.Confirm)
      case "revisit" => (c.get[NodeId]("node"), why).mapN(Command.Revisit(_, _))
      case "gone"    => (c.get[NodeId]("node"), why).mapN(Command.Gone(_, _))
      case other     =>
        Left(DecodingFailure(s"no decision $other: accept, reject, confirm, revisit or gone", c.history))

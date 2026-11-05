package frflow.web.json

import cats.syntax.all.*
import frflow.core.name.NodeId
import frflow.decision.rules.Command
import io.circe.{Decoder, DecodingFailure, HCursor}

/** A decision as the page sends it: `{"action": "accept", "nodes": […], "reason": …, "revisit": […], "seen":
  * {node: version}}`, `reject` with its `node` and the `seen` version, `confirm` with its reason, `revisit` and
  * `gone` with their `node`.
  */
object Asked:
  private given Decoder[NodeId] = Decoder.decodeString.map(NodeId(_))

  given Decoder[Command] = Decoder.instance(c => (c.get[String]("action"), c.get[String]("reason")).tupled
    .flatMap((action, why) => command(c, action, why)))

  private def command(c: HCursor, action: String, why: String): Decoder.Result[Command] = action match
    case "accept"  => (c.get[List[NodeId]]("nodes"), c.getOrElse[List[NodeId]]("revisit")(Nil),
        c.getOrElse[Map[String, String]]("seen")(Map.empty)).mapN((ns, r, seen) =>
        Command.Accept(ns, why, r, seen.map((k, v) => NodeId(k) -> v)))
    case "reject"  => (c.get[NodeId]("node"), c.get[Option[String]]("seen")).mapN(Command.Reject(_, why, _))
    case "confirm" => Right(Command.Confirm(why))
    case "revisit" => c.get[NodeId]("node").map(Command.Revisit(_, why))
    case "gone"    => c.get[NodeId]("node").map(Command.Gone(_, why))
    case other     => Left(DecodingFailure(s"no decision $other: accept, reject, confirm, revisit or gone", c.history))

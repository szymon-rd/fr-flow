package frflow.cli.command

import cats.syntax.all.*
import com.monovore.decline.Opts
import frflow.core.name.NodeId

/** The options FrFlow's commands share, and a layer's commands may use. */
object Options:
  val plain: Opts[Boolean] =
    Opts.flag("plain", "ASCII without colors (also when NO_COLOR is set or the output is not a terminal)").orFalse
  val json: Opts[Boolean] = Opts.flag("json", "print the snapshot (.frflow/kb.json) after it, as JSON").orFalse
  /** A node, by its id: the name of the val it is written in. */
  def node(name: String = "NODE"): Opts[NodeId] = Opts.argument[String](name).map(NodeId(_))
  val nodes: Opts[List[NodeId]] = Opts.arguments[String]("NODE").map(_.toList.map(NodeId(_)))
  val as: Opts[Option[String]] =
    Opts.option[String]("as", "who decides (default: FRFLOW_AS, or the name your key is listed under)").orNone
  val yes: Opts[Boolean] = Opts.flag("yes", "decide without asking (needed without a terminal)", "y").orFalse
  val reason: Opts[Option[String]] =
    Opts.option[String]("reason", "why: kept as part of the theory (asked for on a terminal)", "m").orNone
  val asked: Opts[Asked] = (reason, as, yes).mapN(Asked.apply)
  val revisit: Opts[List[NodeId]] =
    Opts.options[String]("revisit", "a decision below the change that it may affect").orEmpty.map(_.map(NodeId(_)))
  def words(name: String): Opts[String] = Opts.arguments[String](name).map(_.toList.mkString(" "))

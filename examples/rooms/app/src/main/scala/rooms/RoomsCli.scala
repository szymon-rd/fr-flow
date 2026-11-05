package rooms

/** Rooms' command line (`bin/frflow rooms COMMAND`, `sbt "rooms/serve --as NAME"`), over the model in
  * examples/rooms, with no layer on top.
  */
object roomsCli extends frflow.cli.FrFlowApp(rooms, root = "examples/rooms")

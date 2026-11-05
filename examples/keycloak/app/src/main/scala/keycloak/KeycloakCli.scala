package keycloak

/** Keycloak's command line (`bin/frflow keycloak COMMAND`, `sbt "keycloak/serve --as NAME"`), over the model in
  * examples/keycloak, with the AI agent's layer.
  */
object keycloakCli extends frflow.cli.FrFlowApp(knowledge, root = "examples/keycloak",
    extensions = List(frflow.agent.Agent))

package frflow.agent

import frflow.agent.work.AgentApi

/** The AI agent's layer as a project's main object passes it, its files under the project's `.frflow/`
  * (`requests.json`, `conversation.json`; FrFlow never reads them):
  * {{{
  * object authCli extends frflow.cli.FrFlowApp(knowledge, root = "examples/auth",
  *   extensions = List(frflow.agent.Agent))
  * }}}
  */
object Agent extends AgentLayer(host => AgentApi.make(host.reading, host.directory))

package frflow.agent

import frflow.agent.work.AgentApi

/** The AI agent's layer as a project's main object passes it, its files under the project's `.frflow/`
  * (`requests.json`, `conversation.json`; FrFlow never reads them):
  * {{{
  * object roomsCli extends frflow.cli.FrFlowApp(rooms, root = "examples/rooms", extensions = List(frflow.agent.Agent))
  * }}}
  */
object Agent extends AgentLayer(host => AgentApi.make(host.api, host.directory))

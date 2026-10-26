package frflow
package example

/** A suite of examples written as tests, of one knowledge base: `check` finds the compiled suites and reads them. */
trait ExampleSuite:
  def knowledge: KnowledgeBase
  def written: List[Written]

package frflow
package example

/** A suite of examples written as tests, of one FrModel: `check` finds the compiled suites and reads them. */
trait ExampleSuite:
  def knowledge: FrModel
  def written: List[Written]

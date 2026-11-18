package frflow.api

import frflow.api.derive.DocComments

/** A define's meaning is the Scaladoc right above its val, as one line; a val without one has none. */
class DocCommentsSuite extends munit.FunSuite:
  private val source =
    """object Ledger:
      |  /** The balance of the account with this id;
      |    * zero when there is none.
      |    */
      |  val balanceOf = define { (l: Term[Ledger], id: Term[String]) => 0 }
      |
      |  val total = define { (l: Term[Ledger]) => 0 }
      |
      |  /** Not this one. */
      |  def helper = 1
      |  private val owns = define { (l: Term[Ledger]) => true }
      |""".stripMargin

  test("the comment above a val, tidied to one line; none where it has none") {
    assertEquals(DocComments.above("balanceOf", source),
      Some("The balance of the account with this id; zero when there is none."))
    assertEquals(DocComments.above("total", source), None)
    assertEquals(DocComments.above("owns", source), None)
  }

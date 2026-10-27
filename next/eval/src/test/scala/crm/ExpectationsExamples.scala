package crm

import frflow.*

/** What the root is expected to give, on one history (owner §18): it sets no value, so it is checked against the
  * claims in Lean.
  */
class ExpectationsExamples extends FrFlowExamples(knowledge):
  private val ann = Account("ann@acme", TenantId("acme"))
  private val gil = Account("gil@globex", TenantId("globex"))
  private val annContact = CrmRecord(1, TenantId("acme"), Kind.Contact, "Acme contact")
  private val gilDeal = CrmRecord(2, TenantId("globex"), Kind.Deal, "Globex deal")
  private val everything = Ask(Screen.Records, Search.Everything)

  example("When Ann at Acme has added a contact, and Gil at Globex a deal he shared with Acme until 100: at 50 Ann " +
      "finds both, at 150 only her contact, and Gil never finds Ann's contact."):
    ((history === List(Event.Wrote(WriteCmd(ann, Change.Add(annContact))),
        Event.Wrote(WriteCmd(gil, Change.Add(gilDeal))),
        Event.Wrote(WriteCmd(gil, Change.ShareWith(2, TenantId("acme"), Some(100)))))) implies
      (((clock === 50) implies
          (results(ann, everything).contains(annContact) && results(ann, everything).contains(gilDeal))) &&
        ((clock === 150) implies
          (results(ann, everything).contains(annContact) && !results(ann, everything).contains(gilDeal))) &&
        !results(gil, everything).contains(annContact))) is true

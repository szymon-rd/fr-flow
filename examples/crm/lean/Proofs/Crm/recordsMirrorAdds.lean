import FrFlowGen.Crm.recordsMirrorAdds.Spec
import Proofs.Crm.Lemmas

/-! The CRM holds exactly the records users added, by induction over the history (`FrFlow.tracks`, `Runs.store_mirrors`): what the database holds is what its history led
to (`crmRun`, a rule of its state); every store its steps reach holds one row per key (`Runs.stepOf_onePerKey`), so
each step's claims hold of it. A saved write moves the store as one more write moves what users asked: it does what
was asked (`writesTakeEffect`), nothing else (`writesOnlyAsAsked`), and keeps every record (`recordsKept`). A run of
the job leaves the rows of its code's store, which ends exactly the shares whose time has come (`Runs.jobDone_mem`),
as one more run does in what users asked: there, a record has one share per company (`askedIn_unique`). -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Crm.recordsMirrorAdds.Proofs
open Crm Crm.Lemmas

theorem complete : Obl.complete := fun hT hO hK r world h1 h2 h3 =>
  (Runs.store_mirrors hT hO hK world h1 h2 h3).1 r

end Crm.recordsMirrorAdds.Proofs

import FrFlowGen.Crm.storeMirrorsRequests.Spec
import Proofs.Crm.Lemmas

/-! What the CRM holds mirrors what users asked (today's proof), by induction over the history (`FrFlow.tracks`):
what the database holds is what its history led to (`crmRun`, a rule of its state); every store its steps reach holds
one row per key (`Runs.stepOf_onePerKey`), so each step's claims hold of it; it holds the records users added, and
holds a share as current at any time exactly when what users asked shares it then. A saved write moves the store as
one more write moves what users asked: it does what was asked (`writesTakeEffect`), nothing else
(`writesOnlyAsAsked`), and keeps every record (`recordsKept`). A run of the job leaves the rows of its code's store,
which ends exactly the shares whose time has come (`Runs.jobDone_mem`), as one more run does in what users asked:
there, a record has one share per company (`askedIn_unique`). -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Crm.storeMirrorsRequests.Proofs
open Crm Crm.Lemmas

theorem complete : Obl.complete := fun _ hT hO hK _ _ _ => Runs.store_mirrors hT hO hK

end Crm.storeMirrorsRequests.Proofs

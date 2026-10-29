import FrFlowGen.Crm.writeContract.Spec
import Proofs.Crm.Lemmas

/-! `applyWrite` meets writeContract (today's proof): case by case on the change, and on whether its author's
company may make it. A write it may not make returns the store as it was. An add appends the one record asked; a
share or unshare of the author's record replaces only the share, and its time, of that record with the company
named, keeping every other row. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Crm.writeContract.Proofs
open Crm

theorem impl : Obl.impl := Lemmas.applyWrite_contract

end Crm.writeContract.Proofs

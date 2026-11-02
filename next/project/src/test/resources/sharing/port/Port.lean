import FrFlowGen.Old.CanViewContract.Spec
import FrFlowGen.Old.CanEditContract.Spec
import FrFlowGen.Old.InForceContract.Spec
import FrFlowGen.Old.IsOpenContract.Spec
import FrFlowGen.Old.GoneContract.Spec
import FrFlowGen.Old.PendingContract.Spec
import FrFlowGen.Old.ReminderDueContract.Spec
import FrFlowGen.Sharing.canViewContract.Spec
import FrFlowGen.Sharing.canEditContract.Spec
import FrFlowGen.Sharing.inForceContract.Spec
import FrFlowGen.Sharing.isOpenContract.Spec
import FrFlowGen.Sharing.goneContract.Spec
import FrFlowGen.Sharing.pendingContract.Spec
import FrFlowGen.Sharing.reminderDueContract.Spec

/-! Sharing's statements as today's library stated them (`reference/sharing`, in namespace `Old` over the port's
types), against the port's (ARCHITECTURE section 9, equivalence 4): each contract below is proven equivalent, for
every meaning of what it speaks of. The others are listed, not stated here: today's operations' contracts and the
words' definitions spoke of today's defines by today's names (`Sharing.Sharing.accessCode`), whose bodies the port's
defines repeat but whose terms Lean does not identify without unfolding every one; the branches, the deadlines and the
purpose are today's statements over today's run (`Run.after`), the port's over `atEnd` and the code; the three
programs' contracts were stated over today's boundaries' world, the port's over the models' World (owner §36); and
handle's answer is now an option within its time limit, delivery's a race and a bracket (the kept combinators,
ARCHITECTURE 9, step 13). Each listed node's standing and parts are judged in `PortSuite`. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Port
open Sharing

theorem canView_eq (access : Library → Int → PersonId → DocumentId → Option Level)
    (canView : Library → Int → PersonId → DocumentId → Prop) :
    Old.CanViewContract.claim access canView ↔ Sharing.canViewContract.claim canView access := by
  simp only [Old.CanViewContract.claim, Old.CanViewContract.post, Sharing.canViewContract.claim]

theorem canEdit_eq (access : Library → Int → PersonId → DocumentId → Option Level)
    (canEdit : Library → Int → PersonId → DocumentId → Prop) :
    Old.CanEditContract.claim access canEdit ↔ Sharing.canEditContract.claim canEdit access := by
  simp only [Old.CanEditContract.claim, Old.CanEditContract.post, Sharing.canEditContract.claim]

theorem inForce_eq (inForce : Share → Int → Prop) :
    Old.InForceContract.claim inForce ↔ Sharing.inForceContract.claim inForce := by
  simp only [Old.InForceContract.claim, Old.InForceContract.post, Sharing.inForceContract.claim]
  constructor <;> intro h s t <;> rw [h s t] <;> cases s.«until» <;> simp

theorem isOpen_eq (lasts : Int) (isOpen : Invitation → Int → Prop) :
    Old.IsOpenContract.claim lasts isOpen ↔ Sharing.isOpenContract.claim isOpen lasts := by
  simp only [Old.IsOpenContract.claim, Old.IsOpenContract.post, Sharing.isOpenContract.claim]

theorem gone_eq (keeps : Int) (gone : Document → Int → Prop) :
    Old.GoneContract.claim keeps gone ↔ Sharing.goneContract.claim gone keeps := by
  simp only [Old.GoneContract.claim, Old.GoneContract.post, Sharing.goneContract.claim]
  constructor <;> intro h d t <;> rw [h d t] <;> cases d.trashed <;> simp

theorem pending_eq (lasts : Int) (isPending : AccessRequest → Int → Prop) :
    Old.PendingContract.claim lasts isPending ↔ Sharing.pendingContract.claim isPending lasts := by
  simp only [Old.PendingContract.claim, Old.PendingContract.post, Sharing.pendingContract.claim]

theorem reminderDue_eq (after : Int) (reminderDue : AccessRequest → Int → Prop) :
    Old.ReminderDueContract.claim after reminderDue ↔ Sharing.reminderDueContract.claim reminderDue after := by
  simp only [Old.ReminderDueContract.claim, Old.ReminderDueContract.post, Sharing.reminderDueContract.claim]

end Port

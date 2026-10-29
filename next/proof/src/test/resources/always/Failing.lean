namespace Test.endsAfterStart

@[frflow_defs] def keeps_file (file : Booking → (World → ((Except String Unit) × World))) : Prop :=
  (∀ (b : Booking), ((b.start < b.«end») → ((b.start < b.«end») → (∀ (before : World), ((∀ b_1 ∈ before.shelved, (b_1.start < b_1.«end»)) → ((∀ b_1 ∈ before.shelved, (b_1.start < b_1.«end»)) → ((match (file b before) with | (Except.ok result, after) => (∀ b_1 ∈ after.shelved, (b_1.start < b_1.«end»)) | _ => True) ∧ (match (file b before) with | (Except.error error, after) => (∀ b_1 ∈ after.shelved, (b_1.start < b_1.«end»)) | _ => True))))))))

end Test.endsAfterStart

namespace Test.endsAfterStart

@[frflow_defs] def keeps_spoil (spoil : Booking → (World → ((Except String Unit) × World))) : Prop :=
  (∀ (i : Booking), ((i.start < i.«end») → ((i.start < i.«end») → (∀ (before : World), ((∀ b ∈ before.shelved, (b.start < b.«end»)) → ((∀ b ∈ before.shelved, (b.start < b.«end»)) → ((match (spoil i before) with | (Except.ok result, after) => (∀ b ∈ after.shelved, (b.start < b.«end»)) | _ => True) ∧ (match (spoil i before) with | (Except.error error, after) => (∀ b ∈ after.shelved, (b.start < b.«end»)) | _ => True))))))))

end Test.endsAfterStart

namespace Test.endsAfterStart

@[frflow_defs] def keeps_fileTwice (fileTwice : Booking → (World → ((Except String (Unit × Unit)) × World))) : Prop :=
  (∀ (i : Booking), ((i.start < i.«end») → ((i.start < i.«end») → (∀ (before : World), ((∀ b ∈ before.shelved, (b.start < b.«end»)) → ((∀ b ∈ before.shelved, (b.start < b.«end»)) → ((match (fileTwice i before) with | (Except.ok result, after) => (∀ b ∈ after.shelved, (b.start < b.«end»)) | _ => True) ∧ (match (fileTwice i before) with | (Except.error error, after) => (∀ b ∈ after.shelved, (b.start < b.«end»)) | _ => True))))))))

end Test.endsAfterStart

namespace Test.endsAfterStart

@[frflow_defs] def makes_check (check : Booking → (World → ((Except String Booking) × World))) : Prop :=
  (∀ (b : Booking), ((b.start < b.«end») → ((b.start < b.«end») → (∀ (before : World), (match (check b before) with | (Except.ok result, after) => (result.start < result.«end») | _ => True)))))

end Test.endsAfterStart

namespace Test.endsAfterStart

@[frflow_defs] def makes_fileIt_call_0 : Prop :=
  (∀ (b : Booking), ((b.start < b.«end») → ((b.start < b.«end») → (b.start < b.«end»))))

end Test.endsAfterStart

namespace Test.endsAfterStart

@[frflow_defs] def makes_fileBoth_call_0 : Prop :=
  (∀ (b : Booking), ((b.start < b.«end») → ((b.start < b.«end») → (b.start < b.«end»))))

end Test.endsAfterStart

namespace Test.endsAfterStart

@[frflow_defs] def makes_fileBoth_call_1 : Prop :=
  (∀ (b : Booking), ((b.start < b.«end») → ((b.start < b.«end») → (∀ (u : Unit), (b.start < b.«end»)))))

end Test.endsAfterStart

namespace Test.endsAfterStart

@[frflow_defs] def makes_spoilIt_call_0 : Prop :=
  (∀ (b : Booking), ((b.start < b.«end») → ((b.start < b.«end») → (b.start < b.«end»))))

end Test.endsAfterStart

namespace Test.endsAfterStart

@[frflow_defs] def makes_spoilIt_call_1 : Prop :=
  (∀ (b : Booking), ((b.start < b.«end») → ((b.start < b.«end») → (∀ (e : String), ((b.«end» : Int) < (b.start : Int))))))

end Test.endsAfterStart

namespace Test.fromOutside

@[frflow_defs] def keeps_file (file : Booking → (World → ((Except String Unit) × World))) : Prop :=
  (∀ (b : Booking), ((b.start < b.«end») → ((b.start < b.«end») → (∀ (before : World), ((∀ b_1 ∈ before.shelved, (b_1.start < b_1.«end»)) → ((∀ b_1 ∈ before.shelved, (b_1.start < b_1.«end»)) → ((match (file b before) with | (Except.ok result, after) => (∀ b_1 ∈ after.shelved, (b_1.start < b_1.«end»)) | _ => True) ∧ (match (file b before) with | (Except.error error, after) => (∀ b_1 ∈ after.shelved, (b_1.start < b_1.«end»)) | _ => True))))))))

end Test.fromOutside

namespace Test.fromOutside

@[frflow_defs] def keeps_spoil (spoil : Booking → (World → ((Except String Unit) × World))) : Prop :=
  (∀ (i : Booking), ((i.start < i.«end») → ((i.start < i.«end») → (∀ (before : World), ((∀ b ∈ before.shelved, (b.start < b.«end»)) → ((∀ b ∈ before.shelved, (b.start < b.«end»)) → ((match (spoil i before) with | (Except.ok result, after) => (∀ b ∈ after.shelved, (b.start < b.«end»)) | _ => True) ∧ (match (spoil i before) with | (Except.error error, after) => (∀ b ∈ after.shelved, (b.start < b.«end»)) | _ => True))))))))

end Test.fromOutside

namespace Test.fromOutside

@[frflow_defs] def keeps_fileTwice (fileTwice : Booking → (World → ((Except String (Unit × Unit)) × World))) : Prop :=
  (∀ (i : Booking), ((i.start < i.«end») → ((i.start < i.«end») → (∀ (before : World), ((∀ b ∈ before.shelved, (b.start < b.«end»)) → ((∀ b ∈ before.shelved, (b.start < b.«end»)) → ((match (fileTwice i before) with | (Except.ok result, after) => (∀ b ∈ after.shelved, (b.start < b.«end»)) | _ => True) ∧ (match (fileTwice i before) with | (Except.error error, after) => (∀ b ∈ after.shelved, (b.start < b.«end»)) | _ => True))))))))

end Test.fromOutside

namespace Test.fromOutside

@[frflow_defs] def makes_check (check : Booking → (World → ((Except String Booking) × World))) : Prop :=
  (∀ (b : Booking), ((b.start < b.«end») → ((b.start < b.«end») → (∀ (before : World), (match (check b before) with | (Except.ok result, after) => (result.start < result.«end») | _ => True)))))

end Test.fromOutside

namespace Test.fromOutside

@[frflow_defs] def makes_fileIt_call_0 : Prop :=
  (∀ (b : Booking), ((b.start < b.«end») → ((b.start < b.«end») → (b.start < b.«end»))))

end Test.fromOutside

namespace Test.fromOutside

@[frflow_defs] def makes_fileBoth_call_0 : Prop :=
  (∀ (b : Booking), ((b.start < b.«end») → ((b.start < b.«end») → (b.start < b.«end»))))

end Test.fromOutside

namespace Test.fromOutside

@[frflow_defs] def makes_fileBoth_call_1 : Prop :=
  (∀ (b : Booking), ((b.start < b.«end») → ((b.start < b.«end») → (∀ (u : Unit), (b.start < b.«end»)))))

end Test.fromOutside

namespace Test.fromOutside

@[frflow_defs] def makes_spoilIt_call_0 : Prop :=
  (∀ (b : Booking), ((b.start < b.«end») → ((b.start < b.«end») → (b.start < b.«end»))))

end Test.fromOutside

namespace Test.fromOutside

@[frflow_defs] def makes_spoilIt_call_1 : Prop :=
  (∀ (b : Booking), ((b.start < b.«end») → ((b.start < b.«end») → (∀ (e : String), ((b.«end» : Int) < (b.start : Int))))))

end Test.fromOutside

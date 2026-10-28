namespace Test.endsAfterStart

@[frflow_defs] def keeps_file (file : Booking → (World → ((Except String Unit) × World))) : Prop :=
  (∀ (b : Booking), ((b.start < b.«end») → ((b.start < b.«end») → (∀ (before : World), ((∀ b_1 ∈ before.Shelf, (b_1.start < b_1.«end»)) → ((∀ b_1 ∈ before.Shelf, (b_1.start < b_1.«end»)) → ((match (file b before) with | (Except.ok result, after) => (∀ b_1 ∈ after.Shelf, (b_1.start < b_1.«end»)) | _ => True) ∧ (match (file b before) with | (Except.error error, after) => (∀ b_1 ∈ after.Shelf, (b_1.start < b_1.«end»)) | _ => True))))))))

end Test.endsAfterStart

namespace Test.endsAfterStart

@[frflow_defs] def keeps_spoil (spoil : Booking → (World → ((Except String Unit) × World))) : Prop :=
  (∀ (i : Booking), ((i.start < i.«end») → ((i.start < i.«end») → (∀ (before : World), ((∀ b ∈ before.Shelf, (b.start < b.«end»)) → ((∀ b ∈ before.Shelf, (b.start < b.«end»)) → ((match (spoil i before) with | (Except.ok result, after) => (∀ b ∈ after.Shelf, (b.start < b.«end»)) | _ => True) ∧ (match (spoil i before) with | (Except.error error, after) => (∀ b ∈ after.Shelf, (b.start < b.«end»)) | _ => True))))))))

end Test.endsAfterStart

namespace Test.endsAfterStart

@[frflow_defs] def keeps_fileTwice (fileTwice : Booking → (World → ((Except String (Unit × Unit)) × World))) : Prop :=
  (∀ (i : Booking), ((i.start < i.«end») → ((i.start < i.«end») → (∀ (before : World), ((∀ b ∈ before.Shelf, (b.start < b.«end»)) → ((∀ b ∈ before.Shelf, (b.start < b.«end»)) → ((match (fileTwice i before) with | (Except.ok result, after) => (∀ b ∈ after.Shelf, (b.start < b.«end»)) | _ => True) ∧ (match (fileTwice i before) with | (Except.error error, after) => (∀ b ∈ after.Shelf, (b.start < b.«end»)) | _ => True))))))))

end Test.endsAfterStart

namespace Test.endsAfterStart

@[frflow_defs] def makes_check (check : Booking → (World → ((Except String Booking) × World))) : Prop :=
  (∀ (b : Booking), ((b.start < b.«end») → ((b.start < b.«end») → (∀ (before : World), (match (check b before) with | (Except.ok result, after) => (result.start < result.«end») | _ => True)))))

end Test.endsAfterStart

namespace Test.fromOutside

@[frflow_defs] def keeps_file (file : Booking → (World → ((Except String Unit) × World))) : Prop :=
  (∀ (b : Booking), ((b.start < b.«end») → ((b.start < b.«end») → (∀ (before : World), ((∀ b_1 ∈ before.Shelf, (b_1.start < b_1.«end»)) → ((∀ b_1 ∈ before.Shelf, (b_1.start < b_1.«end»)) → ((match (file b before) with | (Except.ok result, after) => (∀ b_1 ∈ after.Shelf, (b_1.start < b_1.«end»)) | _ => True) ∧ (match (file b before) with | (Except.error error, after) => (∀ b_1 ∈ after.Shelf, (b_1.start < b_1.«end»)) | _ => True))))))))

end Test.fromOutside

namespace Test.fromOutside

@[frflow_defs] def keeps_spoil (spoil : Booking → (World → ((Except String Unit) × World))) : Prop :=
  (∀ (i : Booking), ((i.start < i.«end») → ((i.start < i.«end») → (∀ (before : World), ((∀ b ∈ before.Shelf, (b.start < b.«end»)) → ((∀ b ∈ before.Shelf, (b.start < b.«end»)) → ((match (spoil i before) with | (Except.ok result, after) => (∀ b ∈ after.Shelf, (b.start < b.«end»)) | _ => True) ∧ (match (spoil i before) with | (Except.error error, after) => (∀ b ∈ after.Shelf, (b.start < b.«end»)) | _ => True))))))))

end Test.fromOutside

namespace Test.fromOutside

@[frflow_defs] def keeps_fileTwice (fileTwice : Booking → (World → ((Except String (Unit × Unit)) × World))) : Prop :=
  (∀ (i : Booking), ((i.start < i.«end») → ((i.start < i.«end») → (∀ (before : World), ((∀ b ∈ before.Shelf, (b.start < b.«end»)) → ((∀ b ∈ before.Shelf, (b.start < b.«end»)) → ((match (fileTwice i before) with | (Except.ok result, after) => (∀ b ∈ after.Shelf, (b.start < b.«end»)) | _ => True) ∧ (match (fileTwice i before) with | (Except.error error, after) => (∀ b ∈ after.Shelf, (b.start < b.«end»)) | _ => True))))))))

end Test.fromOutside

namespace Test.fromOutside

@[frflow_defs] def makes_check (check : Booking → (World → ((Except String Booking) × World))) : Prop :=
  (∀ (b : Booking), ((b.start < b.«end») → ((b.start < b.«end») → (∀ (before : World), (match (check b before) with | (Except.ok result, after) => (result.start < result.«end») | _ => True)))))

end Test.fromOutside

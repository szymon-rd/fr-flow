namespace Test.endsAfterStart

@[frflow_defs] def keeps_book (book : Booking → (World → (Unit × World))) : Prop :=
  (∀ (b : Booking), ((b.start < b.«end») → ((b.start < b.«end») → (∀ (before : World), ((∀ b_1 ∈ before.stored, (b_1.start < b_1.«end»)) → ((∀ b_1 ∈ before.stored, (b_1.start < b_1.«end»)) → (match (book b before) with | (result, after) => (∀ b_1 ∈ after.stored, (b_1.start < b_1.«end»)))))))))

end Test.endsAfterStart

namespace Test.endsAfterStart

@[frflow_defs] def makes_bookIfFree_call_0 : Prop :=
  (∀ (b : Booking), ((b.start < b.«end») → ((b.start < b.«end») → (b.start < b.«end»))))

end Test.endsAfterStart

namespace Test.fromTheForm

@[frflow_defs] def keeps_book (book : Booking → (World → (Unit × World))) : Prop :=
  (∀ (b : Booking), ((b.start < b.«end») → ((b.start < b.«end») → (∀ (before : World), ((∀ b_1 ∈ before.stored, (b_1.start < b_1.«end»)) → ((∀ b_1 ∈ before.stored, (b_1.start < b_1.«end»)) → (match (book b before) with | (result, after) => (∀ b_1 ∈ after.stored, (b_1.start < b_1.«end»)))))))))

end Test.fromTheForm

namespace Test.fromTheForm

@[frflow_defs] def makes_bookIfFree_call_0 : Prop :=
  (∀ (b : Booking), ((b.start < b.«end») → ((b.start < b.«end») → (b.start < b.«end»))))

end Test.fromTheForm

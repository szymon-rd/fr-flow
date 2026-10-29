namespace Test.endsAfterStart

@[frflow_defs] def keeps_fileBackwards (fileBackwards : Booking → (World → (Unit × World))) : Prop :=
  (∀ (i : Booking), ((i.start < i.«end») → ((i.start < i.«end») → (∀ (before : World), ((∀ b ∈ before.shelved, (b.start < b.«end»)) → ((∀ b ∈ before.shelved, (b.start < b.«end»)) → (match (fileBackwards i before) with | (result, after) => (∀ b ∈ after.shelved, (b.start < b.«end»)))))))))

end Test.endsAfterStart

namespace Test.endsAfterStart

@[frflow_defs] def keeps_countBoth (countBoth : (World → ((Int × Int) × World))) : Prop :=
  (∀ (before : World), ((∀ b ∈ before.shelved, (b.start < b.«end»)) → ((∀ b ∈ before.shelved, (b.start < b.«end»)) → (match (countBoth before) with | (result, after) => (∀ b ∈ after.shelved, (b.start < b.«end»))))))

end Test.endsAfterStart

namespace Test.endsAfterStart

@[frflow_defs] def keeps_putTwo (putTwo : Booking → (World → ((Unit × Unit) × World))) : Prop :=
  (∀ (i : Booking), ((i.start < i.«end») → ((i.start < i.«end») → (∀ (before : World), ((∀ b ∈ before.shelved, (b.start < b.«end»)) → ((∀ b ∈ before.shelved, (b.start < b.«end»)) → (match (putTwo i before) with | (result, after) => (∀ b ∈ after.shelved, (b.start < b.«end»)))))))))

end Test.endsAfterStart

namespace Test.endsAfterStart

@[frflow_defs] def makes_misdate (misdate : Booking → Booking) : Prop :=
  (∀ (x0 : Booking), ((x0.start < x0.«end») → ((x0.start < x0.«end») → ((misdate x0).start < (misdate x0).«end»))))

end Test.endsAfterStart

namespace Test.fromOutside

@[frflow_defs] def keeps_fileBackwards (fileBackwards : Booking → (World → (Unit × World))) : Prop :=
  (∀ (i : Booking), ((i.start < i.«end») → ((i.start < i.«end») → (∀ (before : World), ((∀ b ∈ before.shelved, (b.start < b.«end»)) → ((∀ b ∈ before.shelved, (b.start < b.«end»)) → (match (fileBackwards i before) with | (result, after) => (∀ b ∈ after.shelved, (b.start < b.«end»)))))))))

end Test.fromOutside

namespace Test.fromOutside

@[frflow_defs] def keeps_countBoth (countBoth : (World → ((Int × Int) × World))) : Prop :=
  (∀ (before : World), ((∀ b ∈ before.shelved, (b.start < b.«end»)) → ((∀ b ∈ before.shelved, (b.start < b.«end»)) → (match (countBoth before) with | (result, after) => (∀ b ∈ after.shelved, (b.start < b.«end»))))))

end Test.fromOutside

namespace Test.fromOutside

@[frflow_defs] def keeps_putTwo (putTwo : Booking → (World → ((Unit × Unit) × World))) : Prop :=
  (∀ (i : Booking), ((i.start < i.«end») → ((i.start < i.«end») → (∀ (before : World), ((∀ b ∈ before.shelved, (b.start < b.«end»)) → ((∀ b ∈ before.shelved, (b.start < b.«end»)) → (match (putTwo i before) with | (result, after) => (∀ b ∈ after.shelved, (b.start < b.«end»)))))))))

end Test.fromOutside

namespace Test.fromOutside

@[frflow_defs] def makes_misdate (misdate : Booking → Booking) : Prop :=
  (∀ (x0 : Booking), ((x0.start < x0.«end») → ((x0.start < x0.«end») → ((misdate x0).start < (misdate x0).«end»))))

end Test.fromOutside

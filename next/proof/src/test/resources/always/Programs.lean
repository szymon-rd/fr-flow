namespace Test.endsAfterStart

@[frflow_defs] def makes_reschedule (reschedule : Booking → Booking) : Prop :=
  (∀ (x0 : Booking), ((x0.start < x0.«end») → ((x0.start < x0.«end») → ((reschedule x0).start < (reschedule x0).«end»))))

end Test.endsAfterStart

namespace Test.endsAfterStart

@[frflow_defs] def makes_fetch (fetch : Int → (World → (Booking × World))) : Prop :=
  (∀ (i : Int), (∀ (before : World), (match (fetch i before) with | (result, after) => (result.start < result.«end»))))

end Test.endsAfterStart

namespace Test.endsAfterStart

@[frflow_defs] def makes_latest (latest : (World → (Booking × World))) : Prop :=
  (∀ (before : World), (match (latest before) with | (result, after) => (result.start < result.«end»)))

end Test.endsAfterStart

namespace Test.endsAfterStart

@[frflow_defs] def makes_sample (sample : (List Booking) → Booking) : Prop :=
  (∀ (w : World), ((∀ b ∈ w.Shelf, (b.start < b.«end»)) → ((∀ b ∈ w.Shelf, (b.start < b.«end»)) → ((sample w.Shelf).start < (sample w.Shelf).«end»))))

end Test.endsAfterStart

namespace Test.fromOutside

@[frflow_defs] def makes_reschedule (reschedule : Booking → Booking) : Prop :=
  (∀ (x0 : Booking), ((x0.start < x0.«end») → ((x0.start < x0.«end») → ((reschedule x0).start < (reschedule x0).«end»))))

end Test.fromOutside

namespace Test.fromOutside

@[frflow_defs] def makes_fetch (fetch : Int → (World → (Booking × World))) : Prop :=
  (∀ (i : Int), (∀ (before : World), (match (fetch i before) with | (result, after) => (result.start < result.«end»))))

end Test.fromOutside

namespace Test.fromOutside

@[frflow_defs] def makes_latest (latest : (World → (Booking × World))) : Prop :=
  (∀ (before : World), (match (latest before) with | (result, after) => (result.start < result.«end»)))

end Test.fromOutside

namespace Test.fromOutside

@[frflow_defs] def makes_sample (sample : (List Booking) → Booking) : Prop :=
  (∀ (w : World), ((∀ b ∈ w.Shelf, (b.start < b.«end»)) → ((∀ b ∈ w.Shelf, (b.start < b.«end»)) → ((sample w.Shelf).start < (sample w.Shelf).«end»))))

end Test.fromOutside

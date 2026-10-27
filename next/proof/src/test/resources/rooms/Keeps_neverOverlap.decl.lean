namespace Rooms.neverOverlap

@[frflow_defs] def keeps_book (book : Booking → (World → (Prop × World))) : Prop :=
  (∀ (request : Booking), ((Rooms.endsAfterStart request) → (∀ (before : World), ((Rooms.neverOverlap before.store) → ((∀ b ∈ before.store, (Rooms.endsAfterStart b)) → (match (book request before) with | (result, after) => (Rooms.neverOverlap after.store)))))))

end Rooms.neverOverlap

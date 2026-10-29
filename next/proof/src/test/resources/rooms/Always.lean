namespace Rooms.neverOverlap

@[frflow_defs] def keeps_book (book : Booking → (World → (Prop × World))) : Prop :=
  (∀ (request : Booking), ((Rooms.bookingsEndAfterStart request) → (∀ (before : World), ((Rooms.neverOverlap before.storedBookings) → ((∀ b ∈ before.storedBookings, (Rooms.bookingsEndAfterStart b)) → (match (book request before) with | (result, after) => (Rooms.neverOverlap after.storedBookings)))))))

end Rooms.neverOverlap

namespace Rooms.bookingsOfTheRoom

@[frflow_defs] def makes_inRoom (inRoom : String → (List Booking) → RoomBookings) : Prop :=
  (∀ (room : String), (∀ (w : World), ((Rooms.neverOverlap w.storedBookings) → ((∀ b ∈ w.storedBookings, (Rooms.bookingsEndAfterStart b)) → (Rooms.bookingsOfTheRoom (inRoom room w.storedBookings))))))

end Rooms.bookingsOfTheRoom

namespace Rooms.bookingsOfTheRoom

@[frflow_defs] def makes_bookIfGranted_call_1 : Prop :=
  (∀ (request : Booking), ((Rooms.bookingsEndAfterStart request) → (∀ (r : RoomBookings), ((Rooms.bookingsOfTheRoom r) → ((Rooms.roomBookingsApart r) → ((∀ b ∈ r.bookings, (Rooms.bookingsEndAfterStart b)) → (Rooms.bookingsOfTheRoom r)))))))

end Rooms.bookingsOfTheRoom

namespace Rooms.bookingsOfTheRoom

@[frflow_defs] def makes_bookIfGranted_call_3 : Prop :=
  (∀ (request : Booking), ((Rooms.bookingsEndAfterStart request) → (∀ (r : RoomBookings), ((Rooms.bookingsOfTheRoom r) → ((Rooms.roomBookingsApart r) → ((∀ b ∈ r.bookings, (Rooms.bookingsEndAfterStart b)) → (∀ (x_u : Unit), (Rooms.bookingsOfTheRoom r))))))))

end Rooms.bookingsOfTheRoom

namespace Rooms.roomBookingsApart

@[frflow_defs] def makes_inRoom (inRoom : String → (List Booking) → RoomBookings) : Prop :=
  (∀ (room : String), (∀ (w : World), ((Rooms.neverOverlap w.storedBookings) → ((∀ b ∈ w.storedBookings, (Rooms.bookingsEndAfterStart b)) → (Rooms.roomBookingsApart (inRoom room w.storedBookings))))))

end Rooms.roomBookingsApart

namespace Rooms.roomBookingsApart

@[frflow_defs] def makes_bookIfGranted_call_1 : Prop :=
  (∀ (request : Booking), ((Rooms.bookingsEndAfterStart request) → (∀ (r : RoomBookings), ((Rooms.bookingsOfTheRoom r) → ((Rooms.roomBookingsApart r) → ((∀ b ∈ r.bookings, (Rooms.bookingsEndAfterStart b)) → (Rooms.roomBookingsApart r)))))))

end Rooms.roomBookingsApart

namespace Rooms.roomBookingsApart

@[frflow_defs] def makes_bookIfGranted_call_3 : Prop :=
  (∀ (request : Booking), ((Rooms.bookingsEndAfterStart request) → (∀ (r : RoomBookings), ((Rooms.bookingsOfTheRoom r) → ((Rooms.roomBookingsApart r) → ((∀ b ∈ r.bookings, (Rooms.bookingsEndAfterStart b)) → (∀ (x_u : Unit), (Rooms.roomBookingsApart r))))))))

end Rooms.roomBookingsApart

namespace Rooms.bookingsEndAfterStart

@[frflow_defs] def keeps_book (book : Booking → (World → (Prop × World))) : Prop :=
  (∀ (request : Booking), ((Rooms.bookingsEndAfterStart request) → (∀ (before : World), ((Rooms.neverOverlap before.storedBookings) → ((∀ b ∈ before.storedBookings, (Rooms.bookingsEndAfterStart b)) → (match (book request before) with | (result, after) => (∀ b ∈ after.storedBookings, (Rooms.bookingsEndAfterStart b))))))))

end Rooms.bookingsEndAfterStart

namespace Rooms.bookingsEndAfterStart

@[frflow_defs] def makes_inRoom (inRoom : String → (List Booking) → RoomBookings) : Prop :=
  (∀ (room : String), (∀ (w : World), ((Rooms.neverOverlap w.storedBookings) → ((∀ b ∈ w.storedBookings, (Rooms.bookingsEndAfterStart b)) → (∀ b ∈ (inRoom room w.storedBookings).bookings, (Rooms.bookingsEndAfterStart b))))))

end Rooms.bookingsEndAfterStart

namespace Rooms.bookingsEndAfterStart

@[frflow_defs] def makes_bookIfGranted_call_1 : Prop :=
  (∀ (request : Booking), ((Rooms.bookingsEndAfterStart request) → (∀ (r : RoomBookings), ((Rooms.bookingsOfTheRoom r) → ((Rooms.roomBookingsApart r) → ((∀ b ∈ r.bookings, (Rooms.bookingsEndAfterStart b)) → ((∀ b ∈ r.bookings, (Rooms.bookingsEndAfterStart b)) ∧ (Rooms.bookingsEndAfterStart request))))))))

end Rooms.bookingsEndAfterStart

namespace Rooms.bookingsEndAfterStart

@[frflow_defs] def makes_bookIfGranted_call_2 (granted : RoomBookings → Booking → Prop) : Prop :=
  (∀ (request : Booking), ((Rooms.bookingsEndAfterStart request) → (∀ (r : RoomBookings), ((Rooms.bookingsOfTheRoom r) → ((Rooms.roomBookingsApart r) → ((∀ b ∈ r.bookings, (Rooms.bookingsEndAfterStart b)) → ((granted r request) → (Rooms.bookingsEndAfterStart request))))))))

end Rooms.bookingsEndAfterStart

namespace Rooms.bookingsEndAfterStart

@[frflow_defs] def makes_bookIfGranted_call_3 : Prop :=
  (∀ (request : Booking), ((Rooms.bookingsEndAfterStart request) → (∀ (r : RoomBookings), ((Rooms.bookingsOfTheRoom r) → ((Rooms.roomBookingsApart r) → ((∀ b ∈ r.bookings, (Rooms.bookingsEndAfterStart b)) → (∀ (x_u : Unit), ((∀ b ∈ r.bookings, (Rooms.bookingsEndAfterStart b)) ∧ (Rooms.bookingsEndAfterStart request)))))))))

end Rooms.bookingsEndAfterStart

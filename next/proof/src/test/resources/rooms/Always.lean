namespace Rooms.neverOverlap

@[frflow_defs] def keeps_book (book : Booking → (World → (Prop × World))) : Prop :=
  (∀ (request : Booking), ((Rooms.bookingsEndAfterStart request) → (∀ (before : World), ((Rooms.neverOverlap before.bookingTable) → ((∀ b ∈ before.bookingTable, (Rooms.bookingsEndAfterStart b)) → (match (book request before) with | (result, after) => (Rooms.neverOverlap after.bookingTable)))))))

end Rooms.neverOverlap

namespace Rooms.bookingsOfTheRoom

@[frflow_defs] def makes_inRoom (inRoom : String → (List Booking) → RoomBookings) : Prop :=
  (∀ (room : String), (∀ (w : World), ((Rooms.neverOverlap w.bookingTable) → ((∀ b ∈ w.bookingTable, (Rooms.bookingsEndAfterStart b)) → (Rooms.bookingsOfTheRoom (inRoom room w.bookingTable))))))

end Rooms.bookingsOfTheRoom

namespace Rooms.roomBookingsApart

@[frflow_defs] def makes_inRoom (inRoom : String → (List Booking) → RoomBookings) : Prop :=
  (∀ (room : String), (∀ (w : World), ((Rooms.neverOverlap w.bookingTable) → ((∀ b ∈ w.bookingTable, (Rooms.bookingsEndAfterStart b)) → (Rooms.roomBookingsApart (inRoom room w.bookingTable))))))

end Rooms.roomBookingsApart

namespace Rooms.bookingsEndAfterStart

@[frflow_defs] def keeps_book (book : Booking → (World → (Prop × World))) : Prop :=
  (∀ (request : Booking), ((Rooms.bookingsEndAfterStart request) → (∀ (before : World), ((Rooms.neverOverlap before.bookingTable) → ((∀ b ∈ before.bookingTable, (Rooms.bookingsEndAfterStart b)) → (match (book request before) with | (result, after) => (∀ b ∈ after.bookingTable, (Rooms.bookingsEndAfterStart b))))))))

end Rooms.bookingsEndAfterStart

namespace Rooms.bookingsEndAfterStart

@[frflow_defs] def makes_inRoom (inRoom : String → (List Booking) → RoomBookings) : Prop :=
  (∀ (room : String), (∀ (w : World), ((Rooms.neverOverlap w.bookingTable) → ((∀ b ∈ w.bookingTable, (Rooms.bookingsEndAfterStart b)) → (∀ b ∈ (inRoom room w.bookingTable).bookings, (Rooms.bookingsEndAfterStart b))))))

end Rooms.bookingsEndAfterStart

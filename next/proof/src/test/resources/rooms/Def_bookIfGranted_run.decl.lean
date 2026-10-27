@[frflow_defs] def bookIfGranted_run (granted : RoomBookings → Booking → Prop) : Booking → World → (Prop × World) :=
  fun (request : Booking) (w : World) => (FrFlow.runOn ((Rooms.bookIfGranted granted) request) w)

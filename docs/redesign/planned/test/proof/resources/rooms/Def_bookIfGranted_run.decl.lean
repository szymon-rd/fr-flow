@[frflow_defs] def bookIfGranted_run (granted : RoomBookings → Booking → Prop) : Request → World → (Prop × World) :=
  fun (request : Request) (w : World) => (FrFlow.runOn ((Rooms.bookIfGranted granted) request) w)

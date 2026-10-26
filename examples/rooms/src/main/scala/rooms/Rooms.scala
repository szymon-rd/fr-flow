package rooms

object Rooms:
  def book(held: List[Booking], request: Booking): List[Booking] =
    if held.exists(b => b.room == request.room && b.start < request.end && request.start < b.end) then held
    else held :+ request

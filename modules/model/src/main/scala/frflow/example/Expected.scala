package frflow
package example

/** A call and the answer it must give: `granted(List(Booking("Oak", 9, 10)), Booking("Oak", 10, 11)) is true`. */
final case class Expected(call: Term[?], answer: Any)

package payments

import frflow.*

// The stream's ids: each a type of its own over a string, so one is never given where another is meant. Rocq reads
// each as the string it is over.

/** A payment's id, as its sender gave it: the same for a payment sent twice. */
opaque type PaymentId = String
object PaymentId extends FrSpec.Opaque[PaymentId, String]

/** A card's id. */
opaque type CardId = String
object CardId extends FrSpec.Opaque[CardId, String]

/** A merchant's id. */
opaque type MerchantId = String
object MerchantId extends FrSpec.Opaque[MerchantId, String]

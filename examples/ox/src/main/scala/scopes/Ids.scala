package scopes

import frflow.*

// What a scope and a thread are named by. Rocq reads each as the number it is over.

/** A thread of the JVM. */
opaque type ThreadId = BigInt
object ThreadId extends FrSpec.Opaque[ThreadId, BigInt]

/** A scope: one run of `supervised` or `unsupervised`, from its opening to its end. */
opaque type ScopeId = BigInt
object ScopeId extends FrSpec.Opaque[ScopeId, BigInt]

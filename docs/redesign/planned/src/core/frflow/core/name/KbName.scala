package frflow.core.name

/** A knowledge base's name: the Lean namespace of everything generated for it. */
opaque type KbName = String

object KbName extends Label[KbName]

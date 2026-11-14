package scopes

import frflow.*

// The model: what must hold of a program's scopes and forks (the roots), and what makes it hold.

val scopes: FrModel = FrModel("OxScopes")(
  noForkActsAfterItsScopeIsLeft,
  noForkIsMadeAfterItsScopeIsLeft,
  scopesAreLeftInsideOut,
  startsSound.refines(noForkActsAfterItsScopeIsLeft, noForkIsMadeAfterItsScopeIsLeft, scopesAreLeftInsideOut),
  everyStepCanBeTaken.refines(noForkActsAfterItsScopeIsLeft, noForkIsMadeAfterItsScopeIsLeft,
    scopesAreLeftInsideOut))

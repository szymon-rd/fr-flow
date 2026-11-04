package rooms.walkthrough

import frflow.*

// The README's three changes to rooms (steps 4 to 6 of its walk-through), each a package holding rooms as the
// developer changes it: the calendar, the defines and the nodes the change reaches, the rest rooms' own. Each FrModel
// gives `granted` its code with the same words as rooms', `Calendar(held).grants(request)`, the step's Calendar.

/** Rooms' nodes, `changed` in place of those of the same names. */
def nodes(changed: Node*): List[Node] =
  rooms.rooms.nodes.map(n => changed.find(_.head.id == n.head.id).getOrElse(n))

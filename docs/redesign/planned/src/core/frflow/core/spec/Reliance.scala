package frflow.core.spec

/** How the nodes above a contract stand to it: relied on, or fixing a word they leave open (`.leftOpenAbove`). */
enum Reliance:
  case Relied, LeftOpen

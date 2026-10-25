package frflow

private[frflow] final case class Arm(pat: Pat, body: Tree, tpe: LeanType[?])

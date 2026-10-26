package frflow.testing

/** One node's test run: the settings, and the failing cases kept from earlier runs, tried first. */
final case class Plan(settings: Settings, replay: List[Failure])

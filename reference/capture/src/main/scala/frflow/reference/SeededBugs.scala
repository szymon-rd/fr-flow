package frflow.reference

import java.nio.file.{Files, Path}

/** Writes, for each example named, its seeded bugs and what stops each today, to `DIR/EXAMPLE.txt`:
  * `SeededBugs DIR EXAMPLE...` (run by reference/capture.py). Generated cases use each FrModel's settings.
  */
object SeededBugs:
  private val byExample: Map[String, () => List[Seeded]] = Map(
    "auth" -> (() => AuthBugs.all), "keycloak" -> (() => KeycloakBugs.all), "crm" -> (() => CrmBugs.all),
    "sharing" -> (() => SharingRuns.all))

  def main(args: Array[String]): Unit =
    val dir = Path.of(args.head)
    Files.createDirectories(dir)
    for example <- args.toList.tail do
      val bugs = byExample.getOrElse(example, sys.error(s"no seeded bugs for $example"))()
      val head = List(s"# Seeded bugs: $example", "",
        "Each bug is seeded as today's suite seeds it; under it, what stops it today. Generated cases use the",
        "FrModel's settings (cases and seed shown on each).", "")
      Files.writeString(dir.resolve(s"$example.txt"), (head ++ bugs.flatMap(_.lines)).mkString("", "\n", "\n"))
    // The examples' services may leave threads running (a database's, a runtime's): the run ends here.
    sys.exit(0)

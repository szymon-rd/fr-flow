package frflow
package testing

private[frflow] final class CannotGenerate(what: String) extends RuntimeException(s"cannot generate $what")

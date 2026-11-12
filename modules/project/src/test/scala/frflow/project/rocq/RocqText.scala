package frflow.project.rocq

import scala.annotation.tailrec

/** A Rocq file as its sentences, comments and spacing apart: what two files are compared by. */
object RocqText:
  /** A comment that holds no other. */
  private val Comment = """(?s)\(\*(?:(?!\(\*|\*\)).)*?\*\)""".r
  private val End = """\.(?:\s+|$)""".r
  private val Token = """"[^"]*"|[A-Za-z0-9_.'@%]+|\S""".r

  /** The text without its comments, nested ones included. */
  @tailrec def uncommented(text: String): String =
    val less = Comment.replaceAllIn(text, " ")
    if less == text then text else uncommented(less)

  /** The file's sentences, in order, each as its tokens a space apart. */
  def sentences(text: String): List[String] =
    End.split(uncommented(text)).toList.map(s => Token.findAllIn(s).mkString(" ")).filter(_.nonEmpty)

  /** What a sentence declares: its first two tokens (`Definition forkError`). */
  def declared(sentence: String): String = sentence.split(' ').take(2).mkString(" ")

  /** The sentences between `from` and `until`, both left out. */
  def between(sentences: List[String], from: String, until: String): List[String] =
    sentences.dropWhile(_ != from).drop(1).takeWhile(_ != until)

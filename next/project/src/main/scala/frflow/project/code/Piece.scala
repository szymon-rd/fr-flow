package frflow.project.code

/** A run of Scala source as the simple lexer reads it: code, a literal (a string with its quotes and interpolation
  * holes' text, or a character), or a comment (`//` to the end of its line, or a nested `/* */`).
  */
enum Piece:
  case Code(text: String)
  case Literal(text: String)
  case Comment(text: String)

  def text: String

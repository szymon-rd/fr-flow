package frflow.project.effects.samples

/** An account: a choice that writes fields, `&&` over what only computes. */
final class Account(opening: Int):
  private var balance: Int = opening
  private var refused: Int = 0

  def withdraw(n: Int): Boolean =
    if balance >= n && n > 0 then
      balance = balance - n
      true
    else
      refused = refused + 1
      false

  def deposit(n: Int): Unit = if n > 0 then balance = balance + n

  def total: Int = balance

  def refusals: Int = refused

/** Two accounts: a call's result named and used twice, a loop whose test has an effect, `&&` over a call. */
final class Bank(from: Account, to: Account):
  def transfer(n: Int): Boolean =
    val ok = from.withdraw(n)
    if ok then to.deposit(n)
    ok

  def drain(step: Int): Int =
    var moved = 0
    while from.withdraw(step) do
      to.deposit(step)
      moved = moved + step
    moved

  def drainAtMost(step: Int, times: Int): Int =
    var done = 0
    while done < times && from.withdraw(step) do
      to.deposit(step)
      done = done + 1
    done

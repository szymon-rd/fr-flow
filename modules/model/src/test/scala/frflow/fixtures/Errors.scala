package frflow.fixtures

import frflow.*

/** Errors on flows: a vault whose calls may fail (it is down), flows that raise, handle, retry and guarantee, and
  * their contracts, which say what holds when a run fails as well as when it succeeds.
  */
object Errors:
  /** Why a vault's flow fails: the vault is down, or a withdrawal is more than it holds. */
  enum VaultError:
    case Down, Overdrawn
  object VaultError extends Data[VaultError]

  trait Vault:
    def balance: Flow[BigInt]
    def put(amount: Term[BigInt]): Flow[Unit]

  /** The vault as the proofs see it: the amount it holds. */
  object VaultModel extends Vault, StateModel[BigInt]:
    def balance = state.get
    def put(amount: Term[BigInt]) = state.set(amount)

  /** The vault's own code: it holds the amount, and fails on the calls `faults` says, changing nothing then. */
  final class FlakyVault(start: BigInt, faults: List[Boolean] = Nil) extends Vault:
    private var held = start
    private var left = faults
    def amount: BigInt = held
    private def call[A](f: => A): A =
      val fails = left.headOption.contains(true)
      left = left.drop(1)
      if fails then throw IllegalStateException("the vault is down") else f
    def balance = Flow.effect(call(held))
    def put(amount: Term[BigInt]) = Flow.effect(amount)(a => call { held = a })

  val vault: Boundary[Vault] = Boundary.failing[Vault]("vault", "where the money is kept; it may be down")(VaultError.Down)

  val vaultKept = Node.assumption(vault)(VaultModel)("VaultKept",
    "The vault gives the amount it holds and holds what is put in it; any call may fail because it is down, and then changes nothing.",
    why = "A remote store: a call either happens whole or not at all.")
    .implementedBy(a => FlakyVault(a), _.amount)
  val clockKept = Timing.clockKept

  /** A withdrawal: more than the vault holds is refused (an error), otherwise the rest is kept and given. */
  def withdraw(n: Term[BigInt]): Flow[BigInt] =
    for
      b <- vault.balance
      _ <- (n > b).foldF(Flow.raiseError[Unit](VaultError.Overdrawn: Term[VaultError]), vault.put(b - n))
    yield b - n
  /** A withdrawal that never fails: zero when it did. */
  def safely(n: Term[BigInt]): Flow[BigInt] =
    withdraw(n).attempt[VaultError].map(o => o.fold(_ => BigInt(0): Term[BigInt], r => r))
  /** A deposit tried three times, a second and then two seconds apart. */
  def deposit(n: Term[BigInt]): Flow[Unit] = vault.balance.flatMap(b => vault.put(b + n)).retry[VaultError](Schedule.exponential(1, retries = 2))
  /** A deposit, then a second's rest, whether it went in or not. */
  def depositThenRest(n: Term[BigInt]): Flow[Unit] = vault.put(n).guarantee[VaultError](Flow.sleep(BigInt(1)))

  private val withdrawing = Param[BigInt => Flow[BigInt]]("withdrawing", "a withdrawal from the vault")
  private val withdrawingSafely = Param[BigInt => Flow[BigInt]]("withdrawingSafely", "a withdrawal that never fails")
  private val depositing = Param[BigInt => Flow[Unit]]("depositing", "a deposit, retried")
  private val resting = Param[BigInt => Flow[Unit]]("resting", "a deposit, then a rest")

  private def at(amount: BigInt) = World(VaultModel -> amount, ClockModel -> ClockState(0, Nil))
  private def at(amount: BigInt, now: BigInt) = World(VaultModel -> amount, ClockModel -> ClockState(now, Nil))

  val withdrawContract = Node.contract(withdrawing)("Withdraw",
    "A withdrawal of no more than the vault holds leaves the rest and gives it; one that fails changes nothing.",
    why = "Refused before anything is changed, and the vault's calls change nothing when they fail.")(
    (n, r, before, after) => n <= before(VaultModel) && after(VaultModel) === before(VaultModel) - n && r === after(VaultModel) &&
      after(ClockModel) === before(ClockModel))
    .failsChangingNothing[VaultError]
    .examples()(
      expect(BigInt(3), at(10), BigInt(7), at(7), "three of ten"),
      expect(BigInt(30), at(10), Failed(VaultError.Overdrawn), at(10), "more than it holds"),
      expect(BigInt(3), at(10).failing(false, true), Failed(VaultError.Down), at(10), "the vault is down as the rest is put"),
      reject(BigInt(3), at(10).failing(false, true), Failed(VaultError.Down), at(7), "a failed withdrawal changes nothing"))

  val safelyContract = Node.contract(withdrawingSafely)("WithdrawSafely",
    "A safe withdrawal gives the rest when it could be made, and zero when not; it never fails.",
    why = "attempt turns the withdrawal's errors into its outcome.")(
    (n, r, before, after) => (r === after(VaultModel) && after(VaultModel) === before(VaultModel) - n) ||
      (r === BigInt(0) && after(VaultModel) === before(VaultModel)))
    .onFailure[VaultError]((e, before, after) => False)
    .examples()(
      expect(BigInt(3), at(10), BigInt(7), at(7), "three of ten"),
      expect(BigInt(30), at(10), BigInt(0), at(10), "more than it holds: zero"),
      expect(BigInt(3), at(10).failing(true), BigInt(0), at(10), "the vault is down: zero"),
      reject(BigInt(3), at(10).failing(true), Failed(VaultError.Down), at(10), "it never fails"))

  val depositContract = Node.contract(depositing)("Deposit",
    "A deposit, when it goes in, adds to what the vault held; when every try failed, the vault holds what it held.",
    why = "Each try changes nothing when it fails; the waits between tries move only the clock.")(
    (n, r, before, after) => after(VaultModel) === before(VaultModel) + n)
    .onFailure[VaultError]((e, before, after) => after(VaultModel) === before(VaultModel))
    .examples()(
      expect(BigInt(5), at(10), (), at(15), "in at once"),
      expect(BigInt(5), at(10).failing(true), (), at(15, 1), "the second try, a second later"),
      expect(BigInt(5), at(10).failing(false, true, true), (), at(15, 3), "the third: the first failed as it put, the second as it read"),
      expect(BigInt(5), at(10).failing(true, true, true), Failed(VaultError.Down), at(10, 3), "down three times: the vault keeps what it held"),
      reject(BigInt(5), at(10).failing(true, true, true), Failed(VaultError.Down), at(15, 3), "a deposit that failed is not in"))

  val restContract = Node.contract(resting)("DepositThenRest",
    "A deposit is followed by a second's rest, whether it went in or not.",
    why = "guarantee runs the rest either way.")(
    (n, r, before, after) => after(VaultModel) === n && after(ClockModel).now >= before(ClockModel).now + 1)
    .onFailure[VaultError]((e, before, after) => after(VaultModel) === before(VaultModel) &&
      after(ClockModel).now >= before(ClockModel).now + 1)
    .examples()(
      expect(BigInt(5), at(10), (), at(5, 1), "in, then a rest"),
      expect(BigInt(5), at(10).failing(true), Failed(VaultError.Down), at(10, 1), "down, then a rest all the same"),
      reject(BigInt(5), at(10).failing(true), Failed(VaultError.Down), at(10), "never without the rest"))

  val kb = KnowledgeBase("Errors", idea = "IDEA.md")(vaultKept, clockKept, withdrawContract, safelyContract, depositContract, restContract)
    .implementProven(withdrawContract)((n: Term[BigInt]) => withdraw(n))
    .implementProven(safelyContract)((n: Term[BigInt]) => safely(n))
    .implementProven(depositContract)((n: Term[BigInt]) => deposit(n))
    .implementProven(restContract)((n: Term[BigInt]) => depositThenRest(n))

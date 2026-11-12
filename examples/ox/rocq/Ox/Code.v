(** Ox 1.1.0's scopes and forks, as programs over the JDK's operations.

    Read from `com.softwaremill.ox:core_3:1.1.0`: `ox.internal.ThreadHerd`, `ox.internal.currentScope`,
    `ox.DefaultSupervisor`, `ox.NoOpSupervisor`, `ox.OxError`, `ox.supervised`, `ox.supervisedError`,
    `ox.unsupervised`, `ox.scopedWithCapability`, `ox.runFinalizers`, `ox.fork`, `ox.forkError`, `ox.forkUser`,
    `ox.forkUserError`, `ox.forkUnsupervised`, `ox.Fork.join`.

    Each definition is one method, statement for statement. A class is a record of its fields; a call of a JDK
    method is that method's operation; a lambda or a by-name argument given to code that keeps it is a
    constructor of `code`, its body a case of `interp`; a local `var` is the value threaded through what assigns
    it. *)

From Stdlib Require Import ZArith List Bool String.
Require Import FrFlow.Threads.Prog FrFlow.Threads.Jdk FrFlow.Threads.Sem FrFlow.Threads.Lang.
Import ListNotations.
Open Scope prog_scope.
Open Scope string_scope.
Set Warnings "-register-all".

(** ** The classes *)

Record ThreadHerd := mkThreadHerd {
  ThreadHerd_threadFactory : nat;
  ThreadHerd_herdOwner : tid;
  ThreadHerd_shutdownInProgress : nat;
  ThreadHerd_threads : nat }.

Record DefaultSupervisor := mkDefaultSupervisor {
  DefaultSupervisor_running : nat;
  DefaultSupervisor_result : nat;
  DefaultSupervisor_otherExceptions : nat;
  DefaultSupervisor_otherErrors : nat }.

Inductive Supervisor :=
  | Supervisor_NoOpSupervisor
  | Supervisor_DefaultSupervisor (x : DefaultSupervisor).

Inductive OxError := mkOxError
  (herd : ThreadHerd) (finalizers : nat) (supervisor : Supervisor) (errorMode : nat)
  (parent : option OxError) (locals : nat).

Definition OxError_herd (x : OxError) : ThreadHerd := let (a, _, _, _, _, _) := x in a.
Definition OxError_finalizers (x : OxError) : nat := let (_, a, _, _, _, _) := x in a.
Definition OxError_supervisor (x : OxError) : Supervisor := let (_, _, a, _, _, _) := x in a.
Definition OxError_errorMode (x : OxError) : nat := let (_, _, _, a, _, _) := x in a.
Definition OxError_parent (x : OxError) : option OxError := let (_, _, _, _, a, _) := x in a.
Definition OxError_locals (x : OxError) : nat := let (_, _, _, _, _, a) := x in a.

Inductive Fork := Fork_ForkUsingResult (result : nat).

Inductive obj :=
  | O_OxError (x : OxError)
  | O_Fork (x : Fork)
  | O_ErrorModeSupervisorResult_Success.

(** ** The closures *)

Inductive code :=
  | Lam_ThreadHerd_startThread_1 (this : ThreadHerd) (t : code)
  | Lam_forkError_1 (oxError : OxError) (f : code) (result : nat)
  | Lam_forkUserError_1 (oxError : OxError) (f : code) (result : nat)
  | Lam_forkUnsupervised_1 (oxUnsupervised : OxError) (f : code) (result : nat)
  | Lam_supervisedError_1 (s : DefaultSupervisor) (em : nat) (capability : OxError) (f : code)
  | Lam_supervisedError_2 (f : code) (capability : OxError)
  | Client (n : nat).                    (* a closure of the caller's *)

Abbreviation val := (Jdk.val code obj).
Abbreviation M := (Lang.M code obj).

(** ** Globals and casts *)

Definition currentScope : nat := 0.          (* ox.internal.currentScope: ThreadLocal[OxUnsupervised] *)
Definition oxThreadFactory : nat := 0.       (* ox.oxThreadFactory *)
Definition NoErrorMode : nat := 0.           (* ox.NoErrorMode *)

Definition cast_OxError (v : val) : M OxError :=
  match v with VObj (O_OxError x) => ret x | _ => type_error end.
Definition cast_option_OxError (v : option val) : M (option OxError) :=
  match v with Some v => x <- cast_OxError v ;; ret (Some x) | None => ret None end.
Definition cast_DefaultSupervisor (s : Supervisor) : M DefaultSupervisor :=
  match s with Supervisor_DefaultSupervisor x => ret x | _ => type_error end.
Definition cast_list (v : val) : M (list val) :=
  match v with VList xs => ret xs | _ => type_error end.
Definition is_Success (v : val) : bool :=
  match v with VObj O_ErrorModeSupervisorResult_Success => true | _ => false end.

(** ** ox.ErrorMode: not read. Its methods are taken to touch nothing of the JDK's state here. *)

Definition ErrorMode_isError (this : nat) (f : val) : M bool := extern "ox.ErrorMode.isError".
Definition ErrorMode_getError (this : nat) (f : val) : M val := extern "ox.ErrorMode.getError".
Definition ErrorMode_getT (this : nat) (f : val) : M val := extern "ox.ErrorMode.getT".
Definition ErrorMode_pure (this : nat) (t : val) : M val := extern "ox.ErrorMode.pure".
Definition ErrorMode_pureError (this : nat) (e : val) : M val := extern "ox.ErrorMode.pureError".
Definition ErrorMode_addSuppressedException (this : nat) (error : val) (e : exn) : M val :=
  extern "ox.ErrorMode.addSuppressedException".
Definition ErrorMode_addSuppressedError (this : nat) (error : val) (e : val) : M val :=
  extern "ox.ErrorMode.addSuppressedError".

(** ** ox.internal.ThreadHerd *)

Definition ThreadHerd_new (threadFactory : nat) : M ThreadHerd :=
  herdOwner <- call CurrentThread ;;
  shutdownInProgress <- call (AbNew false) ;;
  threads <- call TsNew ;;
  ret (mkThreadHerd threadFactory herdOwner shutdownInProgress threads).

Definition ThreadHerd_isOwnerOrHerdThread (this : ThreadHerd) (thread : tid) : M bool :=
  if Nat.eqb thread (ThreadHerd_herdOwner this) then ret true
  else call (TsContains (ThreadHerd_threads this) thread).

Definition ThreadHerd_assertNotShuttingDown (this : ThreadHerd) : M unit :=
  x <- call (AbGet (ThreadHerd_shutdownInProgress this)) ;;
  if x then throw IllegalStateException else ret tt.

Definition ThreadHerd_verifyCurrentThreadInScopeTree (this : ThreadHerd) : M unit :=
  currentThread <- call CurrentThread ;;
  let doAssert := fun (scope : OxError) =>
    loop (fun scope : OxError =>
      x <- ThreadHerd_isOwnerOrHerdThread (OxError_herd scope) currentThread ;;
      if x then ret (inr tt)
      else match OxError_parent scope with
           | None => throw IllegalStateException
           | Some parentScope => ret (inl parentScope)
           end) scope in
  x <- call (TlGet currentScope) ;;
  match x with
  | None => throw IllegalStateException
  | Some scope => scope <- cast_OxError scope ;; doAssert scope
  end.

Definition ThreadHerd_assertOnOwnerThread (this : ThreadHerd) : M unit :=
  current <- call CurrentThread ;;
  if negb (Nat.eqb current (ThreadHerd_herdOwner this)) then throw IllegalStateException else ret tt.

Definition ThreadHerd_startThread (this : ThreadHerd) (t : code) : M unit :=
  _ <- ThreadHerd_assertNotShuttingDown this ;;
  _ <- ThreadHerd_verifyCurrentThreadInScopeTree this ;;
  thread <- call (NewThread (Lam_ThreadHerd_startThread_1 this t)) ;;
  _ <- call (TsAdd (ThreadHerd_threads this) thread) ;;
  call (ThreadStart thread).

Definition Lam_ThreadHerd_startThread_1_body (this : ThreadHerd) (t : code) (arg : val) : M val :=
  try_finally (invoke t VUnit)
    (x <- call CurrentThread ;;
     _ <- call (TsRemove (ThreadHerd_threads this) x) ;;
     ret tt).

Definition ThreadHerd_interruptAllAndJoinUntilCompleted (this : ThreadHerd) : M unit :=
  _ <- ThreadHerd_assertOnOwnerThread this ;;
  _ <- call (AbSet (ThreadHerd_shutdownInProgress this) true) ;;
  let interruptedThreads := (@nil tid) in
  let interruptIfNeeded := fun (interruptedThreads : list tid) (t : tid) =>
    if negb (tset_contains interruptedThreads t) then
      _ <- call (ThreadInterrupt t) ;;
      ret (tset_add interruptedThreads t)
    else ret interruptedThreads in
  let interruptedException := (@None exn) in
  st <- while
    (fun st : list tid * option exn =>
      x <- call (TsIsEmpty (ThreadHerd_threads this)) ;;
      ret (negb x))
    (fun st : list tid * option exn => let (interruptedThreads, interruptedException) := st in
      interruptedThreads <- TsForEach (ThreadHerd_threads this)
        (fun (x : tid) (interruptedThreads : list tid) => interruptIfNeeded interruptedThreads x)
        interruptedThreads ;;
      TsForEach (ThreadHerd_threads this)
        (fun (thread : tid) (st : list tid * option exn) => let (interruptedThreads, interruptedException) := st in
          interruptedThreads <- interruptIfNeeded interruptedThreads thread ;;
          interruptedException <- try_catch
            (_ <- call (ThreadJoin thread) ;; ret interruptedException)
            (fun e => match e with
              | InterruptedException =>
                  match interruptedException with
                  | None => ret (Some e)
                  | Some x => _ <- call (AddSuppressed x e) ;; ret interruptedException
                  end
              | _ => throw e
              end) ;;
          ret (interruptedThreads, interruptedException))
        (interruptedThreads, interruptedException))
    (interruptedThreads, interruptedException) ;;
  let (interruptedThreads, interruptedException) := st in
  match interruptedException with
  | Some e => throw e
  | None => ret tt
  end.

(** ** ox.internal.currentLocals, ox.OxError *)

Definition currentLocals : M nat :=
  x <- call (TlGet currentScope) ;;
  match x with
  | None => extern "ox.ForkLocalMap.apply"
  | Some scope => scope <- cast_OxError scope ;; ret (OxError_locals scope)
  end.

Definition OxError_apply (s : Supervisor) (em : nat) (parent : option OxError) (locals : nat) : M OxError :=
  x1 <- ThreadHerd_new oxThreadFactory ;;
  x2 <- call (ArNew (Some (VList []))) ;;
  ret (mkOxError x1 x2 s em parent locals).

Definition OxError_asNoErrorMode (this : OxError) : M OxError :=
  if Nat.eqb (OxError_errorMode this) NoErrorMode then ret this
  else ret (mkOxError (OxError_herd this) (OxError_finalizers this) (OxError_supervisor this) NoErrorMode
              (OxError_parent this) (OxError_locals this)).

(** ** ox.NoOpSupervisor, ox.DefaultSupervisor *)

Definition NoOpSupervisor_forkStarts : M unit := ret tt.
Definition NoOpSupervisor_forkSuccess : M unit := ret tt.
Definition NoOpSupervisor_forkException (e : exn) : M bool := ret false.
Definition NoOpSupervisor_forkAppError (e : val) : M unit := ret tt.

Definition DefaultSupervisor_new : M DefaultSupervisor :=
  running <- call (AiNew 0%Z) ;;
  result <- call CfNew ;;
  otherExceptions <- call EsNew ;;
  otherErrors <- call VsNew ;;
  ret (mkDefaultSupervisor running result otherExceptions otherErrors).

Definition DefaultSupervisor_forkStarts (this : DefaultSupervisor) : M unit :=
  _ <- call (AiIncrementAndGet (DefaultSupervisor_running this)) ;;
  ret tt.

Definition DefaultSupervisor_forkSuccess (this : DefaultSupervisor) : M unit :=
  v <- call (AiDecrementAndGet (DefaultSupervisor_running this)) ;;
  if Z.eqb v 0 then
    _ <- call (CfComplete (DefaultSupervisor_result this) (VObj O_ErrorModeSupervisorResult_Success)) ;;
    ret tt
  else ret tt.

Definition DefaultSupervisor_forkException (this : DefaultSupervisor) (e : exn) : M bool :=
  x <- call (CfCompleteExceptionally (DefaultSupervisor_result this) e) ;;
  _ <- (if negb x then
          _ <- call (EsAdd (DefaultSupervisor_otherExceptions this) e) ;; ret tt
        else ret tt) ;;
  ret true.

Definition DefaultSupervisor_forkAppError (this : DefaultSupervisor) (e : val) : M unit :=
  x <- call (CfComplete (DefaultSupervisor_result this) e) ;;
  if negb x then
    _ <- call (VsAdd (DefaultSupervisor_otherErrors this) e) ;; ret tt
  else ret tt.

Definition DefaultSupervisor_join (this : DefaultSupervisor) : M val :=
  try_catch (call (CfGet (DefaultSupervisor_result this)))
    (fun e => match e with
      | ExecutionException cause => _ <- call (AddSuppressed cause e) ;; throw cause
      | _ => throw e
      end).

Definition DefaultSupervisor_addSuppressedErrors_1 (this : DefaultSupervisor) (e : exn) : M exn :=
  _ <- EsForEach (DefaultSupervisor_otherExceptions this)
    (fun (e2 : exn) (st : unit) =>
      if negb (exn_eqb e e2) then call (AddSuppressed e e2) else ret tt) tt ;;
  _ <- VsForEach (DefaultSupervisor_otherErrors this)
    (fun (e2 : val) (st : unit) => call (AddSuppressed e (Other "ox.SecondaryApplicationError"))) tt ;;
  ret e.

Definition DefaultSupervisor_addSuppressedErrors_2 (this : DefaultSupervisor) (r : val) (errorMode : nat) : M val :=
  let result := r in
  result <- EsForEach (DefaultSupervisor_otherExceptions this)
    (fun (e : exn) (result : val) => ErrorMode_addSuppressedException errorMode result e) result ;;
  result <- VsForEach (DefaultSupervisor_otherErrors this)
    (fun (e : val) (result : val) => ErrorMode_addSuppressedError errorMode result e) result ;;
  ret result.

Definition Supervisor_forkStarts (this : Supervisor) : M unit :=
  match this with
  | Supervisor_NoOpSupervisor => NoOpSupervisor_forkStarts
  | Supervisor_DefaultSupervisor x => DefaultSupervisor_forkStarts x
  end.
Definition Supervisor_forkSuccess (this : Supervisor) : M unit :=
  match this with
  | Supervisor_NoOpSupervisor => NoOpSupervisor_forkSuccess
  | Supervisor_DefaultSupervisor x => DefaultSupervisor_forkSuccess x
  end.
Definition Supervisor_forkException (this : Supervisor) (e : exn) : M bool :=
  match this with
  | Supervisor_NoOpSupervisor => NoOpSupervisor_forkException e
  | Supervisor_DefaultSupervisor x => DefaultSupervisor_forkException x e
  end.
Definition Supervisor_forkAppError (this : Supervisor) (e : val) : M unit :=
  match this with
  | Supervisor_NoOpSupervisor => NoOpSupervisor_forkAppError e
  | Supervisor_DefaultSupervisor x => DefaultSupervisor_forkAppError x e
  end.

(** ** ox.Fork *)

Definition Fork_join (this : Fork) : M val :=
  let (result) := this in
  try_catch (call (CfGet result))
    (fun e => match e with
      | ExecutionException cause => _ <- call (AddSuppressed cause e) ;; throw cause
      | _ => throw e
      end).

(** ** ox.forkError, ox.forkUserError, ox.forkUnsupervised, ox.fork, ox.forkUser *)

Definition forkError (x1 : OxError) (f : code) : M Fork :=
  let oxError := x1 in
  result <- call CfNew ;;
  _ <- ThreadHerd_startThread (OxError_herd oxError) (Lam_forkError_1 oxError f result) ;;
  ret (Fork_ForkUsingResult result).

Definition Lam_forkError_1_body (oxError : OxError) (f : code) (result : nat) (arg : val) : M val :=
  _ <- call (TlSet currentScope (Some (VObj (O_OxError oxError)))) ;;
  let supervisor := OxError_supervisor oxError in
  _ <- try_catch
    (resultOrError <- invoke f VUnit ;;
     let errorMode := OxError_errorMode oxError in
     x <- ErrorMode_isError errorMode resultOrError ;;
     if x then
       x <- ErrorMode_getError errorMode resultOrError ;;
       Supervisor_forkAppError supervisor x
     else
       x <- ErrorMode_getT errorMode resultOrError ;;
       _ <- call (CfComplete result x) ;;
       ret tt)
    (fun e =>
      x <- Supervisor_forkException supervisor e ;;
      if negb x then _ <- call (CfCompleteExceptionally result e) ;; ret tt else ret tt) ;;
  ret VUnit.

Definition forkUserError (x1 : OxError) (f : code) : M Fork :=
  let oxError := x1 in
  result <- call CfNew ;;
  _ <- Supervisor_forkStarts (OxError_supervisor oxError) ;;
  _ <- ThreadHerd_startThread (OxError_herd oxError) (Lam_forkUserError_1 oxError f result) ;;
  ret (Fork_ForkUsingResult result).

Definition Lam_forkUserError_1_body (oxError : OxError) (f : code) (result : nat) (arg : val) : M val :=
  _ <- call (TlSet currentScope (Some (VObj (O_OxError oxError)))) ;;
  supervisor <- cast_DefaultSupervisor (OxError_supervisor oxError) ;;
  _ <- try_catch
    (resultOrError <- invoke f VUnit ;;
     let errorMode := OxError_errorMode oxError in
     x <- ErrorMode_isError errorMode resultOrError ;;
     if x then
       x <- ErrorMode_getError errorMode resultOrError ;;
       DefaultSupervisor_forkAppError supervisor x
     else
       x <- ErrorMode_getT errorMode resultOrError ;;
       _ <- call (CfComplete result x) ;;
       DefaultSupervisor_forkSuccess supervisor)
    (fun e =>
      x <- DefaultSupervisor_forkException supervisor e ;;
      if negb x then _ <- call (CfCompleteExceptionally result e) ;; ret tt else ret tt) ;;
  ret VUnit.

Definition forkUnsupervised (x1 : OxError) (f : code) : M Fork :=
  let oxUnsupervised := x1 in
  result <- call CfNew ;;
  _ <- ThreadHerd_startThread (OxError_herd oxUnsupervised) (Lam_forkUnsupervised_1 oxUnsupervised f result) ;;
  ret (Fork_ForkUsingResult result).

Definition Lam_forkUnsupervised_1_body (oxUnsupervised : OxError) (f : code) (result : nat) (arg : val) : M val :=
  _ <- call (TlSet currentScope (Some (VObj (O_OxError oxUnsupervised)))) ;;
  _ <- try_catch
    (x <- invoke f VUnit ;; _ <- call (CfComplete result x) ;; ret tt)
    (fun e => _ <- call (CfCompleteExceptionally result e) ;; ret tt) ;;
  ret VUnit.

Definition fork (f : code) (x1 : OxError) : M Fork :=
  x <- OxError_asNoErrorMode x1 ;;
  forkError x f.

Definition forkUser (f : code) (x1 : OxError) : M Fork :=
  x <- OxError_asNoErrorMode x1 ;;
  forkUserError x f.

(** ** ox.runFinalizers, ox.scopedWithCapability, ox.unsupervised *)

Definition runFinalizers (scope : OxError) (result : exn + val) : M val :=
  let throwWithSuppressed := fun (es : list exn) =>
    e <- List_head es ;;
    x <- List_tail es ;;
    _ <- List_foreach x (fun x => call (AddSuppressed e x)) ;;
    throw e in
  fs <- call (ArGetAndSet (OxError_finalizers scope) None) ;;
  fs <- unnull fs ;;
  fs <- cast_list fs ;;
  es <- (if List_isEmpty fs then ret (@nil exn)
         else chaos "ox.uninterruptible") ;;
  match result with
  | inl e => throwWithSuppressed (e :: es)
  | inr t => if List_isEmpty es then ret t else throwWithSuppressed es
  end.

Definition scopedWithCapability (capability : OxError) (f : code) : M val :=
  let runWithCurrentScopeSet :=
    result <- try_catch
      (x <- try_finally (invoke f (VObj (O_OxError capability)))
             (ThreadHerd_interruptAllAndJoinUntilCompleted (OxError_herd capability)) ;;
       ret (inr x))
      (fun e => ret (inl e)) ;;
    runFinalizers capability result in
  previousScope <- call (TlGet currentScope) ;;
  try_finally
    (_ <- call (TlSet currentScope (Some (VObj (O_OxError capability)))) ;;
     runWithCurrentScopeSet)
    (call (TlSet currentScope previousScope)).

Definition unsupervised_2 (locals : nat) (f : code) : M val :=
  x <- call (TlGet currentScope) ;;
  x <- cast_option_OxError x ;;
  x <- OxError_apply Supervisor_NoOpSupervisor NoErrorMode x locals ;;
  scopedWithCapability x f.

Definition unsupervised_1 (f : code) : M val :=
  x <- currentLocals ;;
  unsupervised_2 x f.

(** ** ox.supervisedError, ox.supervised *)

Definition supervisedError_2 (em : nat) (locals : nat) (f : code) : M val :=
  s <- DefaultSupervisor_new ;;
  x <- call (TlGet currentScope) ;;
  x <- cast_option_OxError x ;;
  capability <- OxError_apply (Supervisor_DefaultSupervisor s) em x locals ;;
  try_catch
    (scopeResult <- scopedWithCapability capability (Lam_supervisedError_1 s em capability f) ;;
     x <- ErrorMode_isError em scopeResult ;;
     if x then DefaultSupervisor_addSuppressedErrors_2 s scopeResult em else ret scopeResult)
    (fun e =>
      _ <- DefaultSupervisor_addSuppressedErrors_1 s e ;;
      throw e).

Definition Lam_supervisedError_1_body (s : DefaultSupervisor) (em : nat) (capability : OxError) (f : code)
    (arg : val) : M val :=
  mainBodyFork <- forkUserError capability (Lam_supervisedError_2 f capability) ;;
  supervisorResult <- DefaultSupervisor_join s ;;
  if is_Success supervisorResult then
    x <- Fork_join mainBodyFork ;;
    ErrorMode_pure em x
  else ErrorMode_pureError em supervisorResult.

Definition Lam_supervisedError_2_body (f : code) (capability : OxError) (arg : val) : M val :=
  invoke f (VObj (O_OxError capability)).

Definition supervisedError_1 (em : nat) (f : code) : M val :=
  x <- currentLocals ;;
  supervisedError_2 em x f.

Definition supervised (f : code) : M val :=
  supervisedError_1 NoErrorMode f.

(** ** What each closure runs *)

Section Interp.

  (** The caller's closures. *)
  Variable client : nat -> val -> M val.

  Definition interp (c : code) (arg : val) : M val :=
    match c with
    | Lam_ThreadHerd_startThread_1 this t => Lam_ThreadHerd_startThread_1_body this t arg
    | Lam_forkError_1 oxError f result => Lam_forkError_1_body oxError f result arg
    | Lam_forkUserError_1 oxError f result => Lam_forkUserError_1_body oxError f result arg
    | Lam_forkUnsupervised_1 oxUnsupervised f result => Lam_forkUnsupervised_1_body oxUnsupervised f result arg
    | Lam_supervisedError_1 s em capability f => Lam_supervisedError_1_body s em capability f arg
    | Lam_supervisedError_2 f capability => Lam_supervisedError_2_body f capability arg
    | Client n => client n arg
    end.

End Interp.

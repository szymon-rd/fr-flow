(** That `Ox.Gen`, generated, and `Ox.Code`, written by hand, agree: see `RocqAgreement`. Generated. *)

From Stdlib Require Import ZArith List Bool String.
Require Import FrFlow.Threads.Prog FrFlow.Threads.Jdk FrFlow.Threads.Sem FrFlow.Threads.Lang.
Require Import Ox.Code.
Require Ox.Gen.
Import ListNotations.
Open Scope prog_scope.
Open Scope string_scope.
Set Warnings "-register-all".

(** ** The types: each constructor takes the same arguments in both *)

Definition to_code_ThreadHerd (x : Ox.Gen.ThreadHerd) : Ox.Code.ThreadHerd :=
  match x with
  | Ox.Gen.mkThreadHerd a1 a2 a3 a4 => Ox.Code.mkThreadHerd a1 a2 a3 a4
  end.

Definition to_code_DefaultSupervisor (x : Ox.Gen.DefaultSupervisor) : Ox.Code.DefaultSupervisor :=
  match x with
  | Ox.Gen.mkDefaultSupervisor a1 a2 a3 a4 => Ox.Code.mkDefaultSupervisor a1 a2 a3 a4
  end.

Definition to_code_Supervisor (x : Ox.Gen.Supervisor) : Ox.Code.Supervisor :=
  match x with
  | Ox.Gen.Supervisor_NoOpSupervisor => Ox.Code.Supervisor_NoOpSupervisor
  | Ox.Gen.Supervisor_DefaultSupervisor a1 => Ox.Code.Supervisor_DefaultSupervisor (to_code_DefaultSupervisor a1)
  end.

Fixpoint to_code_OxError (x : Ox.Gen.OxError) : Ox.Code.OxError :=
  match x with
  | Ox.Gen.mkOxError a1 a2 a3 a4 a5 a6 => Ox.Code.mkOxError (to_code_ThreadHerd a1) a2 (to_code_Supervisor a3) a4 (match a5 with Some y => Some (to_code_OxError y) | None => None end) a6
  end.

Definition to_code_Fork (x : Ox.Gen.Fork) : Ox.Code.Fork :=
  match x with
  | Ox.Gen.Fork_ForkUsingResult a1 => Ox.Code.Fork_ForkUsingResult a1
  end.

Definition to_code_obj (x : Ox.Gen.obj) : Ox.Code.obj :=
  match x with
  | Ox.Gen.O_OxError a1 => Ox.Code.O_OxError (to_code_OxError a1)
  | Ox.Gen.O_Fork a1 => Ox.Code.O_Fork (to_code_Fork a1)
  | Ox.Gen.O_ErrorModeSupervisorResult_Success => Ox.Code.O_ErrorModeSupervisorResult_Success
  end.

Fixpoint to_code_code (x : Ox.Gen.code) : Ox.Code.code :=
  match x with
  | Ox.Gen.Lam_ThreadHerd_startThread_1 a1 a2 => Ox.Code.Lam_ThreadHerd_startThread_1 (to_code_ThreadHerd a1) (to_code_code a2)
  | Ox.Gen.Lam_forkError_1 a1 a2 a3 => Ox.Code.Lam_forkError_1 (to_code_OxError a1) (to_code_code a2) a3
  | Ox.Gen.Lam_forkUserError_1 a1 a2 a3 => Ox.Code.Lam_forkUserError_1 (to_code_OxError a1) (to_code_code a2) a3
  | Ox.Gen.Lam_forkUnsupervised_1 a1 a2 a3 => Ox.Code.Lam_forkUnsupervised_1 (to_code_OxError a1) (to_code_code a2) a3
  | Ox.Gen.Lam_supervisedError_1 a1 a2 a3 a4 => Ox.Code.Lam_supervisedError_1 (to_code_DefaultSupervisor a1) a2 (to_code_OxError a3) (to_code_code a4)
  | Ox.Gen.Lam_supervisedError_2 a1 a2 => Ox.Code.Lam_supervisedError_2 (to_code_code a1) (to_code_OxError a2)
  | Ox.Gen.Client a1 a2 => Ox.Code.Client a1 (List.map (fun y => (to_code_OxError y)) a2)
  end.

Definition of_code_ThreadHerd (x : Ox.Code.ThreadHerd) : Ox.Gen.ThreadHerd :=
  match x with
  | Ox.Code.mkThreadHerd a1 a2 a3 a4 => Ox.Gen.mkThreadHerd a1 a2 a3 a4
  end.

Definition of_code_DefaultSupervisor (x : Ox.Code.DefaultSupervisor) : Ox.Gen.DefaultSupervisor :=
  match x with
  | Ox.Code.mkDefaultSupervisor a1 a2 a3 a4 => Ox.Gen.mkDefaultSupervisor a1 a2 a3 a4
  end.

Definition of_code_Supervisor (x : Ox.Code.Supervisor) : Ox.Gen.Supervisor :=
  match x with
  | Ox.Code.Supervisor_NoOpSupervisor => Ox.Gen.Supervisor_NoOpSupervisor
  | Ox.Code.Supervisor_DefaultSupervisor a1 => Ox.Gen.Supervisor_DefaultSupervisor (of_code_DefaultSupervisor a1)
  end.

Fixpoint of_code_OxError (x : Ox.Code.OxError) : Ox.Gen.OxError :=
  match x with
  | Ox.Code.mkOxError a1 a2 a3 a4 a5 a6 => Ox.Gen.mkOxError (of_code_ThreadHerd a1) a2 (of_code_Supervisor a3) a4 (match a5 with Some y => Some (of_code_OxError y) | None => None end) a6
  end.

Definition of_code_Fork (x : Ox.Code.Fork) : Ox.Gen.Fork :=
  match x with
  | Ox.Code.Fork_ForkUsingResult a1 => Ox.Gen.Fork_ForkUsingResult a1
  end.

Definition of_code_obj (x : Ox.Code.obj) : Ox.Gen.obj :=
  match x with
  | Ox.Code.O_OxError a1 => Ox.Gen.O_OxError (of_code_OxError a1)
  | Ox.Code.O_Fork a1 => Ox.Gen.O_Fork (of_code_Fork a1)
  | Ox.Code.O_ErrorModeSupervisorResult_Success => Ox.Gen.O_ErrorModeSupervisorResult_Success
  end.

Fixpoint of_code_code (x : Ox.Code.code) : Ox.Gen.code :=
  match x with
  | Ox.Code.Lam_ThreadHerd_startThread_1 a1 a2 => Ox.Gen.Lam_ThreadHerd_startThread_1 (of_code_ThreadHerd a1) (of_code_code a2)
  | Ox.Code.Lam_forkError_1 a1 a2 a3 => Ox.Gen.Lam_forkError_1 (of_code_OxError a1) (of_code_code a2) a3
  | Ox.Code.Lam_forkUserError_1 a1 a2 a3 => Ox.Gen.Lam_forkUserError_1 (of_code_OxError a1) (of_code_code a2) a3
  | Ox.Code.Lam_forkUnsupervised_1 a1 a2 a3 => Ox.Gen.Lam_forkUnsupervised_1 (of_code_OxError a1) (of_code_code a2) a3
  | Ox.Code.Lam_supervisedError_1 a1 a2 a3 a4 => Ox.Gen.Lam_supervisedError_1 (of_code_DefaultSupervisor a1) a2 (of_code_OxError a3) (of_code_code a4)
  | Ox.Code.Lam_supervisedError_2 a1 a2 => Ox.Gen.Lam_supervisedError_2 (of_code_code a1) (of_code_OxError a2)
  | Ox.Code.Client a1 a2 => Ox.Gen.Client a1 (List.map (fun y => (of_code_OxError y)) a2)
  end.

(** ** The generated definitions, over the hand-written file's types *)

Module Over.

Definition OxError_herd (x : OxError) : ThreadHerd := let (a, _, _, _, _, _) := x in a.

Definition OxError_finalizers (x : OxError) : nat := let (_, a, _, _, _, _) := x in a.

Definition OxError_supervisor (x : OxError) : Supervisor := let (_, _, a, _, _, _) := x in a.

Definition OxError_errorMode (x : OxError) : nat := let (_, _, _, a, _, _) := x in a.

Definition OxError_parent (x : OxError) : option OxError := let (_, _, _, _, a, _) := x in a.

Definition OxError_locals (x : OxError) : nat := let (_, _, _, _, _, a) := x in a.

(** ** Globals and casts *)

Definition currentScope : nat := 0.

Definition oxThreadFactory : nat := 0.

Definition NoErrorMode : nat := 0.

Definition cast_OxError (v : val) : M OxError :=
  match v with VObj (O_OxError x) => ret x | _ => type_error end.

Definition cast_option_OxError (v : option val) : M (option OxError) :=
  match v with Some v => x <- cast_OxError v ;; ret (Some x) | None => ret None end.

Definition cast_DefaultSupervisor (s : Supervisor) : M DefaultSupervisor :=
  match s with Supervisor_DefaultSupervisor x => ret x | _ => type_error end.

Definition cast_list (v : val) : M (list val) := match v with VList xs => ret xs | _ => type_error end.

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
  let doAssert :=
    fun (scope : OxError) =>
      loop
        (fun scope : OxError =>
           x <- ThreadHerd_isOwnerOrHerdThread (OxError_herd scope) currentThread ;;
           if x then ret (inr tt)
           else
             match OxError_parent scope with
             | None => throw IllegalStateException
             | Some parentScope => ret (inl parentScope)
             end) scope in
  x <- call (TlGet currentScope) ;;
  match x with
  | None => throw IllegalStateException
  | Some scope =>
      scope <- cast_OxError scope ;;
      doAssert scope
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
    (x <- call CurrentThread ;; _ <- call (TsRemove (ThreadHerd_threads this) x) ;; ret tt).

Definition ThreadHerd_interruptAllAndJoinUntilCompleted (this : ThreadHerd) : M unit :=
  _ <- ThreadHerd_assertOnOwnerThread this ;;
  _ <- call (AbSet (ThreadHerd_shutdownInProgress this) true) ;;
  let interruptedThreads := (@nil tid) in
  let interruptIfNeeded :=
    fun (interruptedThreads : list tid) (t : tid) =>
      if negb (tset_contains interruptedThreads t) then
        _ <- call (ThreadInterrupt t) ;;
        ret (tset_add interruptedThreads t)
      else ret interruptedThreads in
  let interruptedException := (@None exn) in
  st <- while (fun st : list tid * option exn => x <- call (TsIsEmpty (ThreadHerd_threads this)) ;; ret (negb x))
      (fun st : list tid * option exn =>
         let (interruptedThreads, interruptedException) := st in
         interruptedThreads <- TsForEach (ThreadHerd_threads this)
             (fun (x : tid) (interruptedThreads : list tid) => interruptIfNeeded interruptedThreads x)
             interruptedThreads ;;
         TsForEach (ThreadHerd_threads this)
           (fun (thread : tid) (st : list tid * option exn) =>
              let (interruptedThreads, interruptedException) := st in
              interruptedThreads <- interruptIfNeeded interruptedThreads thread ;;
              interruptedException <- try_catch (_ <- call (ThreadJoin thread) ;; ret interruptedException)
                  (fun e =>
                     match e with
                     | InterruptedException =>
                         match interruptedException with
                         | None => ret (Some e)
                         | Some x =>
                             _ <- call (AddSuppressed x e) ;;
                             ret interruptedException
                         end
                     | _ => throw e
                     end) ;;
              ret (interruptedThreads, interruptedException)) (interruptedThreads, interruptedException))
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
  | Some scope =>
      scope <- cast_OxError scope ;;
      ret (OxError_locals scope)
  end.

Definition OxError_apply (s : Supervisor) (em : nat) (parent : option OxError) (locals : nat) : M OxError :=
  x1 <- ThreadHerd_new oxThreadFactory ;;
  x2 <- call (ArNew (Some (VList []))) ;;
  ret (mkOxError x1 x2 s em parent locals).

Definition OxError_asNoErrorMode (this : OxError) : M OxError :=
  if Nat.eqb (OxError_errorMode this) NoErrorMode then ret this
  else
    ret
      (mkOxError (OxError_herd this) (OxError_finalizers this) (OxError_supervisor this) NoErrorMode
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
  _ <- (if negb x then _ <- call (EsAdd (DefaultSupervisor_otherExceptions this) e) ;; ret tt else ret tt) ;;
  ret true.

Definition DefaultSupervisor_forkAppError (this : DefaultSupervisor) (e : val) : M unit :=
  x <- call (CfComplete (DefaultSupervisor_result this) e) ;;
  if negb x then _ <- call (VsAdd (DefaultSupervisor_otherErrors this) e) ;; ret tt else ret tt.

Definition DefaultSupervisor_join (this : DefaultSupervisor) : M val :=
  try_catch (call (CfGet (DefaultSupervisor_result this)))
    (fun e =>
       match e with
       | ExecutionException cause =>
           _ <- call (AddSuppressed cause e) ;;
           throw cause
       | _ => throw e
       end).

Definition DefaultSupervisor_addSuppressedErrors_1 (this : DefaultSupervisor) (e : exn) : M exn :=
  _ <- EsForEach (DefaultSupervisor_otherExceptions this)
      (fun (e2 : exn) (st : unit) => if negb (exn_eqb e e2) then call (AddSuppressed e e2) else ret tt) tt ;;
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
    (fun e =>
       match e with
       | ExecutionException cause =>
           _ <- call (AddSuppressed cause e) ;;
           throw cause
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

Definition forkUnsupervised (f : code) (x1 : OxError) : M Fork :=
  let oxUnsupervised := x1 in
  result <- call CfNew ;;
  _ <- ThreadHerd_startThread (OxError_herd oxUnsupervised) (Lam_forkUnsupervised_1 oxUnsupervised f result) ;;
  ret (Fork_ForkUsingResult result).

Definition Lam_forkUnsupervised_1_body (oxUnsupervised : OxError) (f : code) (result : nat) (arg : val) : M val :=
  _ <- call (TlSet currentScope (Some (VObj (O_OxError oxUnsupervised)))) ;;
  _ <- try_catch (x <- invoke f VUnit ;; _ <- call (CfComplete result x) ;; ret tt)
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
  let throwWithSuppressed :=
    fun (es : list exn) =>
      e <- List_head es ;;
      x <- List_tail es ;;
      _ <- List_foreach x (fun x => call (AddSuppressed e x)) ;;
      throw e in
  fs <- call (ArGetAndSet (OxError_finalizers scope) None) ;;
  fs <- unnull fs ;;
  fs <- cast_list fs ;;
  es <- (if List_isEmpty fs then ret (@nil exn) else chaos "ox.uninterruptible") ;;
  match result with
  | inl e => throwWithSuppressed (e :: es)
  | inr t => if List_isEmpty es then ret t else throwWithSuppressed es
  end.

Definition scopedWithCapability (capability : OxError) (f : code) : M val :=
  let runWithCurrentScopeSet :=
    result <- try_catch
        (x <- try_finally (invoke f (VObj (O_OxError capability)))
             (ThreadHerd_interruptAllAndJoinUntilCompleted (OxError_herd capability)) ;;
         ret (inr x)) (fun e => ret (inl e)) ;;
    runFinalizers capability result in
  previousScope <- call (TlGet currentScope) ;;
  try_finally (_ <- call (TlSet currentScope (Some (VObj (O_OxError capability)))) ;; runWithCurrentScopeSet)
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
    (fun e => _ <- DefaultSupervisor_addSuppressedErrors_1 s e ;; throw e).

Definition Lam_supervisedError_1_body (s : DefaultSupervisor) (em : nat) (capability : OxError) (f : code) (arg : val) : M val :=
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

Definition supervised (f : code) : M val := supervisedError_1 NoErrorMode f.

(** ** What each closure runs *)

Section Interp.

  (** The caller's closures. *)
  Variable client : nat -> list OxError -> val -> M val.

  Definition interp (c : code) (arg : val) : M val :=
    match c with
    | Lam_ThreadHerd_startThread_1 this t => Lam_ThreadHerd_startThread_1_body this t arg
    | Lam_forkError_1 oxError f result => Lam_forkError_1_body oxError f result arg
    | Lam_forkUserError_1 oxError f result => Lam_forkUserError_1_body oxError f result arg
    | Lam_forkUnsupervised_1 oxUnsupervised f result => Lam_forkUnsupervised_1_body oxUnsupervised f result arg
    | Lam_supervisedError_1 s em capability f => Lam_supervisedError_1_body s em capability f arg
    | Lam_supervisedError_2 f capability => Lam_supervisedError_2_body f capability arg
    | Client n caps => client n caps arg
    end.

End Interp.

End Over.

(** ** Each is the hand-written definition of its name *)

Lemma OxError_herd_agrees : @Over.OxError_herd = @Ox.Code.OxError_herd. Proof. reflexivity. Qed.
Lemma OxError_finalizers_agrees : @Over.OxError_finalizers = @Ox.Code.OxError_finalizers. Proof. reflexivity. Qed.
Lemma OxError_supervisor_agrees : @Over.OxError_supervisor = @Ox.Code.OxError_supervisor. Proof. reflexivity. Qed.
Lemma OxError_errorMode_agrees : @Over.OxError_errorMode = @Ox.Code.OxError_errorMode. Proof. reflexivity. Qed.
Lemma OxError_parent_agrees : @Over.OxError_parent = @Ox.Code.OxError_parent. Proof. reflexivity. Qed.
Lemma OxError_locals_agrees : @Over.OxError_locals = @Ox.Code.OxError_locals. Proof. reflexivity. Qed.
Lemma currentScope_agrees : @Over.currentScope = @Ox.Code.currentScope. Proof. reflexivity. Qed.
Lemma oxThreadFactory_agrees : @Over.oxThreadFactory = @Ox.Code.oxThreadFactory. Proof. reflexivity. Qed.
Lemma NoErrorMode_agrees : @Over.NoErrorMode = @Ox.Code.NoErrorMode. Proof. reflexivity. Qed.
Lemma cast_OxError_agrees : @Over.cast_OxError = @Ox.Code.cast_OxError. Proof. reflexivity. Qed.
Lemma cast_option_OxError_agrees : @Over.cast_option_OxError = @Ox.Code.cast_option_OxError. Proof. reflexivity. Qed.
Lemma cast_DefaultSupervisor_agrees : @Over.cast_DefaultSupervisor = @Ox.Code.cast_DefaultSupervisor. Proof. reflexivity. Qed.
Lemma cast_list_agrees : @Over.cast_list = @Ox.Code.cast_list. Proof. reflexivity. Qed.
Lemma is_Success_agrees : @Over.is_Success = @Ox.Code.is_Success. Proof. reflexivity. Qed.
Lemma ErrorMode_isError_agrees : @Over.ErrorMode_isError = @Ox.Code.ErrorMode_isError. Proof. reflexivity. Qed.
Lemma ErrorMode_getError_agrees : @Over.ErrorMode_getError = @Ox.Code.ErrorMode_getError. Proof. reflexivity. Qed.
Lemma ErrorMode_getT_agrees : @Over.ErrorMode_getT = @Ox.Code.ErrorMode_getT. Proof. reflexivity. Qed.
Lemma ErrorMode_pure_agrees : @Over.ErrorMode_pure = @Ox.Code.ErrorMode_pure. Proof. reflexivity. Qed.
Lemma ErrorMode_pureError_agrees : @Over.ErrorMode_pureError = @Ox.Code.ErrorMode_pureError. Proof. reflexivity. Qed.
Lemma ErrorMode_addSuppressedException_agrees : @Over.ErrorMode_addSuppressedException = @Ox.Code.ErrorMode_addSuppressedException. Proof. reflexivity. Qed.
Lemma ErrorMode_addSuppressedError_agrees : @Over.ErrorMode_addSuppressedError = @Ox.Code.ErrorMode_addSuppressedError. Proof. reflexivity. Qed.
Lemma ThreadHerd_new_agrees : @Over.ThreadHerd_new = @Ox.Code.ThreadHerd_new. Proof. reflexivity. Qed.
Lemma ThreadHerd_isOwnerOrHerdThread_agrees : @Over.ThreadHerd_isOwnerOrHerdThread = @Ox.Code.ThreadHerd_isOwnerOrHerdThread. Proof. reflexivity. Qed.
Lemma ThreadHerd_assertNotShuttingDown_agrees : @Over.ThreadHerd_assertNotShuttingDown = @Ox.Code.ThreadHerd_assertNotShuttingDown. Proof. reflexivity. Qed.
Lemma ThreadHerd_verifyCurrentThreadInScopeTree_agrees : @Over.ThreadHerd_verifyCurrentThreadInScopeTree = @Ox.Code.ThreadHerd_verifyCurrentThreadInScopeTree. Proof. reflexivity. Qed.
Lemma ThreadHerd_assertOnOwnerThread_agrees : @Over.ThreadHerd_assertOnOwnerThread = @Ox.Code.ThreadHerd_assertOnOwnerThread. Proof. reflexivity. Qed.
Lemma ThreadHerd_startThread_agrees : @Over.ThreadHerd_startThread = @Ox.Code.ThreadHerd_startThread. Proof. reflexivity. Qed.
Lemma Lam_ThreadHerd_startThread_1_body_agrees : @Over.Lam_ThreadHerd_startThread_1_body = @Ox.Code.Lam_ThreadHerd_startThread_1_body. Proof. reflexivity. Qed.
Lemma ThreadHerd_interruptAllAndJoinUntilCompleted_agrees : @Over.ThreadHerd_interruptAllAndJoinUntilCompleted = @Ox.Code.ThreadHerd_interruptAllAndJoinUntilCompleted. Proof. reflexivity. Qed.
Lemma currentLocals_agrees : @Over.currentLocals = @Ox.Code.currentLocals. Proof. reflexivity. Qed.
Lemma OxError_apply_agrees : @Over.OxError_apply = @Ox.Code.OxError_apply. Proof. reflexivity. Qed.
Lemma OxError_asNoErrorMode_agrees : @Over.OxError_asNoErrorMode = @Ox.Code.OxError_asNoErrorMode. Proof. reflexivity. Qed.
Lemma NoOpSupervisor_forkStarts_agrees : @Over.NoOpSupervisor_forkStarts = @Ox.Code.NoOpSupervisor_forkStarts. Proof. reflexivity. Qed.
Lemma NoOpSupervisor_forkSuccess_agrees : @Over.NoOpSupervisor_forkSuccess = @Ox.Code.NoOpSupervisor_forkSuccess. Proof. reflexivity. Qed.
Lemma NoOpSupervisor_forkException_agrees : @Over.NoOpSupervisor_forkException = @Ox.Code.NoOpSupervisor_forkException. Proof. reflexivity. Qed.
Lemma NoOpSupervisor_forkAppError_agrees : @Over.NoOpSupervisor_forkAppError = @Ox.Code.NoOpSupervisor_forkAppError. Proof. reflexivity. Qed.
Lemma DefaultSupervisor_new_agrees : @Over.DefaultSupervisor_new = @Ox.Code.DefaultSupervisor_new. Proof. reflexivity. Qed.
Lemma DefaultSupervisor_forkStarts_agrees : @Over.DefaultSupervisor_forkStarts = @Ox.Code.DefaultSupervisor_forkStarts. Proof. reflexivity. Qed.
Lemma DefaultSupervisor_forkSuccess_agrees : @Over.DefaultSupervisor_forkSuccess = @Ox.Code.DefaultSupervisor_forkSuccess. Proof. reflexivity. Qed.
Lemma DefaultSupervisor_forkException_agrees : @Over.DefaultSupervisor_forkException = @Ox.Code.DefaultSupervisor_forkException. Proof. reflexivity. Qed.
Lemma DefaultSupervisor_forkAppError_agrees : @Over.DefaultSupervisor_forkAppError = @Ox.Code.DefaultSupervisor_forkAppError. Proof. reflexivity. Qed.
Lemma DefaultSupervisor_join_agrees : @Over.DefaultSupervisor_join = @Ox.Code.DefaultSupervisor_join. Proof. reflexivity. Qed.
Lemma DefaultSupervisor_addSuppressedErrors_1_agrees : @Over.DefaultSupervisor_addSuppressedErrors_1 = @Ox.Code.DefaultSupervisor_addSuppressedErrors_1. Proof. reflexivity. Qed.
Lemma DefaultSupervisor_addSuppressedErrors_2_agrees : @Over.DefaultSupervisor_addSuppressedErrors_2 = @Ox.Code.DefaultSupervisor_addSuppressedErrors_2. Proof. reflexivity. Qed.
Lemma Supervisor_forkStarts_agrees : @Over.Supervisor_forkStarts = @Ox.Code.Supervisor_forkStarts. Proof. reflexivity. Qed.
Lemma Supervisor_forkSuccess_agrees : @Over.Supervisor_forkSuccess = @Ox.Code.Supervisor_forkSuccess. Proof. reflexivity. Qed.
Lemma Supervisor_forkException_agrees : @Over.Supervisor_forkException = @Ox.Code.Supervisor_forkException. Proof. reflexivity. Qed.
Lemma Supervisor_forkAppError_agrees : @Over.Supervisor_forkAppError = @Ox.Code.Supervisor_forkAppError. Proof. reflexivity. Qed.
Lemma Fork_join_agrees : @Over.Fork_join = @Ox.Code.Fork_join. Proof. reflexivity. Qed.
Lemma forkError_agrees : @Over.forkError = @Ox.Code.forkError. Proof. reflexivity. Qed.
Lemma Lam_forkError_1_body_agrees : @Over.Lam_forkError_1_body = @Ox.Code.Lam_forkError_1_body. Proof. reflexivity. Qed.
Lemma forkUserError_agrees : @Over.forkUserError = @Ox.Code.forkUserError. Proof. reflexivity. Qed.
Lemma Lam_forkUserError_1_body_agrees : @Over.Lam_forkUserError_1_body = @Ox.Code.Lam_forkUserError_1_body. Proof. reflexivity. Qed.
Lemma forkUnsupervised_agrees : (fun x1 f => @Over.forkUnsupervised f x1) = @Ox.Code.forkUnsupervised. Proof. reflexivity. Qed.
Lemma Lam_forkUnsupervised_1_body_agrees : @Over.Lam_forkUnsupervised_1_body = @Ox.Code.Lam_forkUnsupervised_1_body. Proof. reflexivity. Qed.
Lemma fork_agrees : @Over.fork = @Ox.Code.fork. Proof. reflexivity. Qed.
Lemma forkUser_agrees : @Over.forkUser = @Ox.Code.forkUser. Proof. reflexivity. Qed.
Lemma runFinalizers_agrees : @Over.runFinalizers = @Ox.Code.runFinalizers. Proof. reflexivity. Qed.
Lemma scopedWithCapability_agrees : @Over.scopedWithCapability = @Ox.Code.scopedWithCapability. Proof. reflexivity. Qed.
Lemma unsupervised_2_agrees : @Over.unsupervised_2 = @Ox.Code.unsupervised_2. Proof. reflexivity. Qed.
Lemma unsupervised_1_agrees : @Over.unsupervised_1 = @Ox.Code.unsupervised_1. Proof. reflexivity. Qed.
Lemma supervisedError_2_agrees : @Over.supervisedError_2 = @Ox.Code.supervisedError_2. Proof. reflexivity. Qed.
Lemma Lam_supervisedError_1_body_agrees : @Over.Lam_supervisedError_1_body = @Ox.Code.Lam_supervisedError_1_body. Proof. reflexivity. Qed.
Lemma Lam_supervisedError_2_body_agrees : @Over.Lam_supervisedError_2_body = @Ox.Code.Lam_supervisedError_2_body. Proof. reflexivity. Qed.
Lemma supervisedError_1_agrees : @Over.supervisedError_1 = @Ox.Code.supervisedError_1. Proof. reflexivity. Qed.
Lemma supervised_agrees : @Over.supervised = @Ox.Code.supervised. Proof. reflexivity. Qed.
Lemma interp_agrees : @Over.interp = @Ox.Code.interp. Proof. reflexivity. Qed.

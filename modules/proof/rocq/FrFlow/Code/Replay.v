(** An execution written out, produced from the code.

    Writing out an execution by hand is long, and what its references are (the functions the code makes among
    them) is longer. Both follow from the code, given what is outside it: which calls are made from outside, at
    which moments each thread acts, and what each call of what is outside the code answers. `replay` goes through
    a call's program with these, as an execution of it would, and gives the references and the places of the
    objects made; `trace` prints the events too, so that they can be written into a statement. Nothing here is
    trusted: an execution so produced is then shown to be one of the code, as any other (`Witness`). *)

From FrFlow Require Import Executions.
From Stdlib Require Import String List ZArith Bool.
Require Import FrFlow.Threads.Prog FrFlow.Jvm.Machine.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Program FrFlow.Scala.Table FrFlow.Scala.Value.
Require Import FrFlow.Scala.Meaning FrFlow.Scala.Library.
Require Import FrFlow.Code.Outside FrFlow.Code.Conforms FrFlow.Code.Classes FrFlow.Code.Walk FrFlow.Code.Witness.
Require Import FrFlow.Code.Names.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

(** What a call of what is outside the code answers: at once; as a call made and responded to at the thread's
    next moment; or made, then its last argument (a function) applied to each of some values, then responded to. *)
Inductive Ans :=
  | Atom (v : val)
  | Slow (v : val)
  | Each (m : string) (xs : list val) (v : val).

Definition Heap := list ((nat * string) * val).
Fixpoint heap_get (h : Heap) (r : nat) (f : string) : val :=
  match h with
  | [] => VObj Null
  | ((r', f'), v) :: rest => if (Nat.eqb r r' && String.eqb f f')%bool then v else heap_get rest r f
  end.
Definition heap_new (h : Heap) (r : nat) (fields : list (string * val)) : Heap :=
  (map (fun fv => ((r, fst fv), snd fv)) fields ++ h)%list.
Fixpoint class_of_place (ps : list (nat * string)) (r : nat) : string :=
  match ps with [] => "?" | (r', c) :: rest => if Nat.eqb r r' then c else class_of_place rest r end.

(** A value, short enough to read. *)
Inductive Short := Fun (s : sym) | ByName | Plain (v : val).
Definition short (v : val) : Short :=
  match v with
  | VCode (Fn (DefDef s _ _ _ _ _) _ _) => Fun s
  | VCode (Fn _ _ _) => Fun NoSym
  | VCode (Thunk _ _) => ByName
  | _ => Plain v
  end.

Ltac settle_head T p :=
  let q := eval lazy head beta iota zeta delta in p in
  lazymatch q with
  | Call (Init ?cls) ?arg ?k => settle_head T (pbind (run T (Init cls) arg) k)
  | Call (Thunk ?b ?sc) (VList []) ?k => settle_head T (pbind (run T (Thunk b sc) (VList [])) k)
  | Iter ?body ?s ?k => settle_head T (unfold_iter body s k)
  | _ => q
  end.

Ltac respond say a w w2 x refs :=
  lazymatch x with
  | inr ?v =>
      let e2 := eval lazy in (Event_Respond a w (Response_Returned (name_of refs v)) []) in say w2 e2
  | inl ?ex => idtac "THROWN AT" w2 ":" ex
  end.

(* walk T say a i p refs moments heap places answers cont: the events of the call made at i by a, running p. cont takes
   the result and the state left (refs, moments, heap, places, answers). *)
Ltac walk T say a i p refs moments heap places answers cont :=
  let q := settle_head T p in
  lazymatch q with
  | Ret ?x => cont x refs moments heap places answers
  | Vis ?o ?k =>
      let o' := eval lazy in o in
      lazymatch moments with
      | ?w :: ?ms =>
        lazymatch o' with
        | ObjNew ?cls ?fs =>
            let r := eval lazy in (List.length places) in
            let refs1 := eval lazy in (extend refs (vref cls r :: map snd fs)) in
            let e := eval lazy in (Event_Make a (Some i) (name_of refs1 (vref cls r)) cls
              (map (fun fv => Held_mk (field_label T cls (fst fv)) (name_of refs1 (snd fv))) fs)) in
            say w e;
            let heap' := eval lazy in (heap_new heap r fs) in
            let places' := eval lazy in (places ++ [(r, cls)])%list in
            walk T say a i (k (inr r)) refs1 ms heap' places' answers cont
        | ObjGet ?r ?f =>
            let cls := eval lazy in (class_of_place places r) in
            let v := eval lazy in (heap_get heap r f) in
            let e := eval lazy in (Event_Read a (Some i) (name_of refs (vref cls r))
              (field_label T cls f) (name_of refs v)) in
            say w e;
            walk T say a i (k (inr v)) refs ms heap places answers cont
        | ObjMark ?r ?f =>
            let cls := eval lazy in (class_of_place places r) in
            let e := eval lazy in (Event_Mark a (Some i) (name_of refs (vref cls r)) (field_label T cls f)) in
            say w e;
            walk T say a i (k (inr tt)) refs ms heap places answers cont
        | ObjSet ?r ?f ?v =>
            let cls := eval lazy in (class_of_place places r) in
            let refs1 := eval lazy in (extend refs [v]) in
            let e := eval lazy in (Event_Write a (Some i) (name_of refs1 (vref cls r))
              (field_label T cls f) (name_of refs1 v)) in
            say w e;
            let heap' := eval lazy in (((r, f), v) :: heap) in
            walk T say a i (k (inr tt)) refs1 ms heap' places answers cont
        | ExtCall _ ?m ?args =>
            lazymatch answers with
            | Atom ?v :: ?rest =>
                let refs1 := eval lazy in (extend refs (args ++ [v])%list) in
                let e := eval lazy in (Event_Atomic a (Some i) (Invocation_mk m (map (name_of refs1) args))
                  (Response_Returned (name_of refs1 v)) []) in
                say w e;
                walk T say a i (k (inr v)) refs1 ms heap places rest cont
            | Slow ?v :: ?rest =>
                let refs1 := eval lazy in (extend refs (args ++ [v])%list) in
                let e := eval lazy in (Event_Invoke a (Some i) (Invocation_mk m (map (name_of refs1) args))) in
                say w e;
                lazymatch ms with
                | ?w2 :: ?ms2 =>
                    let e2 := eval lazy in (Event_Respond a w (Response_Returned (name_of refs1 v)) []) in
                    say w2 e2;
                    walk T say a i (k (inr v)) refs1 ms2 heap places rest cont
                end
            | Each ?m2 ?xs ?v :: ?rest =>
                let refs1 := eval lazy in (extend refs (args ++ [v])%list) in
                let e := eval lazy in (Event_Invoke a (Some i) (Invocation_mk m (map (name_of refs1) args))) in
                say w e;
                let fv := eval lazy in (last args VUnit) in
                lazymatch fv with
                | VCode ?c =>
                    let rec each xs refsE msE heapE placesE answersE :=
                      lazymatch xs with
                      | [] =>
                          lazymatch msE with
                          | ?w2 :: ?ms2 =>
                              let e2 := eval lazy in (Event_Respond a w (Response_Returned (name_of refsE v)) []) in
                              say w2 e2;
                              walk T say a i (k (inr v)) refsE ms2 heapE placesE answersE cont
                          end
                      | ?x :: ?xs' =>
                          lazymatch msE with
                          | ?w1 :: ?ms1 =>
                              let refsE1 := eval lazy in (extend refsE [x]) in
                              let e1 := eval lazy in (Event_Invoke a (Some w)
                                (Invocation_mk m2 [name_of refsE1 (VCode c); name_of refsE1 x])) in
                              say w1 e1;
                              walk T say a w1 (run T c (VList [x])) refsE1 ms1 heapE placesE answersE
                                ltac:(fun r refsF msF heapF placesF answersF =>
                                  lazymatch msF with
                                  | ?w3 :: ?ms3 =>
                                      let r' := eval lazy in r in
                                      respond say a w1 w3 r' refsF;
                                      each xs' refsF ms3 heapF placesF answersF
                                  end)
                          end
                      end in
                    each xs refs1 ms heap places rest
                end
            | _ => idtac "NEED ANSWER FOR" m; cont (inr VUnit : exn + val) refs moments heap places answers
            end
        end
      | _ => idtac "OUT OF MOMENTS"; cont (inr VUnit : exn + val) refs moments heap places answers
      end
  | Call (Method ?s) ?arg ?k =>
      lazymatch moments with
      | ?w :: ?ms =>
          let arg' := eval lazy in arg in
          lazymatch arg' with
          | VList (?on :: ?args) =>
              let refs1 := eval lazy in (extend refs (on :: args)) in
              let e := eval lazy in (Event_Invoke a (Some i)
                (Invocation_mk (label_of s) (map (name_of refs1) (receiver on ++ args)%list))) in
              say w e;
              walk T say a w (run T (Method s) arg') refs1 ms heap places answers
                ltac:(fun x refs2 ms1 heap1 places1 answers1 =>
                  lazymatch ms1 with
                  | ?w2 :: ?ms2 =>
                      let x' := eval lazy in x in
                      let refs3 := lazymatch x' with
                        | inr ?v => eval lazy in (extend refs2 [v]) | _ => refs2 end in
                      respond say a w w2 x' refs3;
                      walk T say a i (k x') refs3 ms2 heap1 places1 answers1 cont
                  | _ => idtac "OUT OF MOMENTS"; cont (inr VUnit : exn + val) refs2 ms1 heap1 places1 answers1
                  end)
          end
      | _ => idtac "OUT OF MOMENTS"; cont (inr VUnit : exn + val) refs moments heap places answers
      end
  | Call ?c ?arg ?k =>
      lazymatch moments with
      | ?w :: ?ms =>
          let arg' := eval lazy in arg in
          let m := lazymatch c with
            | Thunk _ _ => lazymatch arg' with VUnit => constr:(by_name_apply) | _ => constr:(function_apply) end
            | _ => constr:(function_apply)
            end in
          let refs1 := eval lazy in (extend refs (VCode c :: arguments arg')) in
          let e := eval lazy in (Event_Invoke a (Some i)
            (Invocation_mk m (name_of refs1 (VCode c) :: map (name_of refs1) (arguments arg')))) in
          say w e;
          walk T say a w (run T c arg') refs1 ms heap places answers
            ltac:(fun x refs2 ms1 heap1 places1 answers1 =>
              lazymatch ms1 with
              | ?w2 :: ?ms2 =>
                  let x' := eval lazy in x in
                  let refs3 := lazymatch x' with
                    | inr ?v => eval lazy in (extend refs2 [v]) | _ => refs2 end in
                  respond say a w w2 x' refs3;
                  walk T say a i (k x') refs3 ms2 heap1 places1 answers1 cont
              | _ => idtac "OUT OF MOMENTS"; cont (inr VUnit : exn + val) refs2 ms1 heap1 places1 answers1
              end)
      | _ => idtac "OUT OF MOMENTS"; cont (inr VUnit : exn + val) refs moments heap places answers
      end
  end.

(** A call from outside the code, made at the first moment given by `a` on the values `on` (its method `m`),
    which runs `p`: the call, its events, its response. What is left is posed under the names given. *)
Ltac top T say a inside m on p refs moments heap places answers nr nh np :=
  lazymatch moments with
  | ?w :: ?ms =>
      let refs1 := eval lazy in (extend refs on) in
      let e := eval lazy in (Event_Invoke a inside (Invocation_mk m (map (name_of refs1) on))) in
      say w e;
      walk T say a w p refs1 ms heap places answers
        ltac:(fun x refs2 ms1 heap1 places1 answers1 =>
          let x' := eval lazy in x in
          let refs3 := lazymatch x' with | inr ?v => eval lazy in (extend refs2 [v]) | _ => refs2 end in
          lazymatch ms1 with
          | ?w2 :: ?ms2 =>
              respond say a w w2 x' refs3;
              lazymatch ms2 with [] => idtac | _ => idtac "MOMENTS LEFT" ms2 end;
              lazymatch answers1 with [] => idtac | _ => idtac "ANSWERS LEFT" answers1 end
          | _ => idtac "NO MOMENT FOR THE RESPONSE"
          end;
          pose (nr := refs3); pose (nh := heap1); pose (np := places1))
  end.

Ltac show_refs refs := let r := eval lazy in (map (fun kv => (fst kv, short (snd kv))) refs) in idtac "REFS" r.
Ltac show_places ps := let r := eval lazy in ps in idtac "PLACES" r.

(** The function a reference names. *)
Ltac fn_of refs n name :=
  let v := eval lazy in (ref_at refs n) in
  lazymatch v with Some (VCode ?c) => pose (name := c) end.

(** `trace` prints each event; `replay` only goes through. *)
Ltac trace T a inside m on p refs moments heap places answers nr nh np :=
  top T ltac:(fun w e => idtac "EV" w ":" e) a inside m on p refs moments heap places answers nr nh np.
Ltac replay T a inside m on p refs moments heap places answers nr nh np :=
  top T ltac:(fun w e => idtac) a inside m on p refs moments heap places answers nr nh np.

(** The class of the object at each place, from the places written. *)
Definition places_of (ps : list (nat * string)) (r : nat) : string := class_of_place ps r.

(** The function a reference names, or one that does nothing where it names none. *)
Definition fn_at (refs : list (Z * val)) (n : Z) : code :=
  match ref_at refs n with Some (VCode c) => c | _ => Thunk (Literal CUnit) [] end.

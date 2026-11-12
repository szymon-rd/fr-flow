Require Export FrFlowGen.Auth.Domain.

(** What the proofs of auth share: a token's holder. The holder is the user of a session under the token; and,
    when the table issues each token to one user, the holder of a session's token is that session's user. *)

(** The holder of a token is the user of a session under it. *)
Lemma Lemmas_session_of_holder (sessions : Sessions) (t : string) (u : UserId) :
  holderOf sessions t = Some u -> exists s, In s (open_of sessions) /\ token_of s = t /\ user_of s = u.
Proof.
  unfold holderOf. destruct (List_find _ _) as [s |] eqn:hf; [| discriminate].
  intros [= <-]. unfold List_find in hf. apply find_some in hf. destruct hf as [hm hd].
  exists s. split; [exact hm |]. split; [| reflexivity].
  unfold decide in hd. destruct (excluded_middle_informative _) as [e |]; [exact e | discriminate].
Qed.

(** With each token issued once, the session found under a session's token is that session. *)
Lemma Lemmas_find_session (l : list Session) :
  List_Pairwise (fun a b => ~ token_of a = token_of b) l -> forall s, In s l ->
  List_find (fun x => decide (token_of x = token_of s)) l = Some s.
Proof.
  unfold List_Pairwise, List_find, decide. induction 1 as [| y ys hy _ ih]; intros s hm.
  - destruct hm.
  - simpl. destruct hm as [-> | hm].
    + destruct (excluded_middle_informative _); [reflexivity | contradiction].
    + destruct (excluded_middle_informative _) as [e | _].
      * exfalso. rewrite Forall_forall in hy. exact (hy s hm e).
      * apply ih. exact hm.
Qed.

(** With each token issued once, the holder of a session's token is that session's user. *)
Lemma Lemmas_holder_of_session (sessions : Sessions) :
  tokensIssuedOnce sessions -> forall s, In s (open_of sessions) ->
  holderOf sessions (token_of s) = Some (user_of s).
Proof. intros hs s hm. unfold holderOf. rewrite (Lemmas_find_session _ hs s hm). reflexivity. Qed.

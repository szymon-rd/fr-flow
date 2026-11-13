Require Export FrFlowGen.Auth.Whole.Spec.

(** The condition of `grantLetsIn` FrFlow's search found no values for, shown to hold of values given here: a
    session table with one session, Ann's under the token `t`, and a grant table with one grant, Ann's for
    `/docs`. Each token is issued once, there being one, and the holder of `t` has a grant for `/docs`. *)

Lemma Whole_Proofs_satisfiable_1_grantLetsIn : Whole_Obl_satisfiable_1_grantLetsIn.
Proof.
  unfold Whole_Obl_satisfiable_1_grantLetsIn.
  exists (Sessions_mk [Session_mk "t" (UserId_mk "ann")]).
  exists [Grant_mk (UserId_mk "ann") (Path_mk "/docs")].
  split.
  - unfold tokensIssuedOnce, List_Pairwise. cbn. repeat constructor.
  - exists "t"%string. exists (Path_mk "/docs"). repeat split.
    exists (UserId_mk "ann"). split.
    + unfold holderOf, List_find, decide. cbn.
      destruct (excluded_middle_informative ("t"%string = "t"%string)) as [_ | n]; [reflexivity | contradiction n].
      reflexivity.
    + unfold grantFor. eexists. split; [left; reflexivity | reflexivity].
Qed.

(** Staged: 54 programs. Left to the meaning of the tree: 0. *)

From Stdlib Require Import String List ZArith.
Require Import FrFlow.Jvm.Prog FrFlow.Jvm.Machine.
Require Import FrFlow.Scala.Tree FrFlow.Scala.Program FrFlow.Scala.Table FrFlow.Scala.Value FrFlow.Scala.Meaning.
Require FrFlow.Code.Staged.
Import ListNotations.
Open Scope string_scope.
Open Scope meaning_scope.

Section Units.

  Variable T : table.

  Definition init_Account_new_1 (this : val) (args : list val) : D :=
    sc <~ Staged.captured T this ;;
    match args with
    | [opening_1] =>
        _ <~ Staged.set_field T this "opening" opening_1 ;;
        balance_2 <~ Staged.get_field T this "opening" ;;
        _ <~ Staged.set_field T this "balance" balance_2 ;;
        _ <~ Staged.set_field T this "refused" (vint (0)%Z) ;;
        Staged.give VUnit
    | _ =>
        stuck "a call given other than what the definition takes"
    end.

  Definition m_Account_withdraw_3 (this : val) (args : list val) : D :=
    sc <~ Staged.captured T this ;;
    match args with
    | [n_1] =>
        test_4 <~ (on_3 <~ (on_2 <~ Staged.get_field T this "balance" ;;
              Staged.out T (Member "scala.Int" ">=" "scala.Int:scala.Boolean") on_2 [] [n_1]) ;;
           Staged.out_lazy T (Member "scala.Boolean" "&&" "scala.Boolean:scala.Boolean") on_3 []
             [
               inl (VCode (Thunk (Ident (Local "<by-name>" 2)) ([("n#1", n_1); ("this:frflow.project.effects.samples.Account", this); ("this:java.lang.Object", this)] ++ sc)%list))
             ]) ;;
        match test_4 with
        | VBool true =>
            _ <~ (value_6 <~ (on_5 <~ Staged.get_field T this "balance" ;;
                  Staged.out T (Member "scala.Int" "-" "scala.Int:scala.Int") on_5 [] [n_1]) ;;
               Staged.set_field T this "balance" value_6) ;;
            Staged.give (VBool true)
        | VBool false =>
            _ <~ (value_8 <~ (on_7 <~ Staged.get_field T this "refused" ;;
                  Staged.out T (Member "scala.Int" "+" "scala.Int:scala.Int") on_7 [] [(vint (1)%Z)]) ;;
               Staged.set_field T this "refused" value_8) ;;
            Staged.give (VBool false)
        | _ =>
            stuck "a condition that gave no truth value"
        end
    | _ =>
        stuck "a call given other than what the definition takes"
    end.

  Definition by_name_2 (sc : scope) : D :=
    Staged.out T (Member "scala.Int" ">" "scala.Int:scala.Boolean") (Staged.found sc "n#1") [] [(vint (0)%Z)].

  Definition m_Account_deposit_4 (this : val) (args : list val) : D :=
    sc <~ Staged.captured T this ;;
    match args with
    | [n_1] =>
        test_2 <~ Staged.out T (Member "scala.Int" ">" "scala.Int:scala.Boolean") n_1 [] [(vint (0)%Z)] ;;
        match test_2 with
        | VBool true =>
            value_4 <~ (on_3 <~ Staged.get_field T this "balance" ;;
               Staged.out T (Member "scala.Int" "+" "scala.Int:scala.Int") on_3 [] [n_1]) ;;
            Staged.set_field T this "balance" value_4
        | VBool false =>
            Staged.give VUnit
        | _ =>
            stuck "a condition that gave no truth value"
        end
    | _ =>
        stuck "a call given other than what the definition takes"
    end.

  Definition m_Account_total_5 (this : val) (args : list val) : D :=
    sc <~ Staged.captured T this ;;
    match args with
    | [] =>
        Staged.get_field T this "balance"
    | _ =>
        stuck "a call given other than what the definition takes"
    end.

  Definition m_Account_refusals_6 (this : val) (args : list val) : D :=
    sc <~ Staged.captured T this ;;
    match args with
    | [] =>
        Staged.get_field T this "refused"
    | _ =>
        stuck "a call given other than what the definition takes"
    end.

  Definition init_Bank_new_7 (this : val) (args : list val) : D :=
    sc <~ Staged.captured T this ;;
    match args with
    | [from_1; to_2] =>
        _ <~ Staged.set_field T this "from" from_1 ;;
        _ <~ Staged.set_field T this "to" to_2 ;;
        Staged.give VUnit
    | _ =>
        stuck "a call given other than what the definition takes"
    end.

  Definition m_Bank_transfer_8 (this : val) (args : list val) : D :=
    sc <~ Staged.captured T this ;;
    match args with
    | [n_1] =>
        ok_3 <~ (on_2 <~ Staged.get_field T this "from" ;;
           Staged.call_method T (Member "frflow.project.effects.samples.Account" "withdraw" "scala.Int:scala.Boolean") on_2 [n_1]) ;;
        _ <~ (match ok_3 with
           | VBool true =>
               on_4 <~ Staged.get_field T this "to" ;;
               Staged.call_method T (Member "frflow.project.effects.samples.Account" "deposit" "scala.Int:scala.Unit") on_4 [n_1]
           | VBool false =>
               Staged.give VUnit
           | _ =>
               stuck "a condition that gave no truth value"
           end) ;;
        Staged.give ok_3
    | _ =>
        stuck "a call given other than what the definition takes"
    end.

  Definition m_Bank_drain_9 (this : val) (args : list val) : D :=
    sc <~ Staged.captured T this ;;
    match args with
    | [step_1] =>
        moved_2 <~ Staged.new_var T "<var>:scala.Int" (vint (0)%Z) ;;
        _ <~ (Staged.while_ T
             (on_3 <~ Staged.get_field T this "from" ;;
              Staged.call_method T (Member "frflow.project.effects.samples.Account" "withdraw" "scala.Int:scala.Boolean") on_3 [step_1])
             (_ <~ (on_4 <~ Staged.get_field T this "to" ;;
                 Staged.call_method T (Member "frflow.project.effects.samples.Account" "deposit" "scala.Int:scala.Unit") on_4 [step_1]) ;;
              value_6 <~ (on_5 <~ Staged.held T moved_2 ;;
                 Staged.out T (Member "scala.Int" "+" "scala.Int:scala.Int") on_5 [] [step_1]) ;;
              Staged.set_var T moved_2 value_6)) ;;
        Staged.held T moved_2
    | _ =>
        stuck "a call given other than what the definition takes"
    end.

  Definition m_Bank_drainAtMost_11 (this : val) (args : list val) : D :=
    sc <~ Staged.captured T this ;;
    match args with
    | [step_1; times_2] =>
        done_3 <~ Staged.new_var T "<var>:scala.Int" (vint (0)%Z) ;;
        _ <~ (Staged.while_ T
             (on_5 <~ (on_4 <~ Staged.held T done_3 ;;
                 Staged.out T (Member "scala.Int" "<" "scala.Int:scala.Boolean") on_4 [] [times_2]) ;;
              Staged.out_lazy T (Member "scala.Boolean" "&&" "scala.Boolean:scala.Boolean") on_5 []
                [
                  inl (VCode (Thunk (Ident (Local "<by-name>" 10)) ([("done#8", done_3); ("step#6", step_1); ("this:frflow.project.effects.samples.Bank", this); ("this:java.lang.Object", this); ("times#7", times_2)] ++ sc)%list))
                ])
             (_ <~ (on_6 <~ Staged.get_field T this "to" ;;
                 Staged.call_method T (Member "frflow.project.effects.samples.Account" "deposit" "scala.Int:scala.Unit") on_6 [step_1]) ;;
              value_8 <~ (on_7 <~ Staged.held T done_3 ;;
                 Staged.out T (Member "scala.Int" "+" "scala.Int:scala.Int") on_7 [] [(vint (1)%Z)]) ;;
              Staged.set_var T done_3 value_8)) ;;
        Staged.held T done_3
    | _ =>
        stuck "a call given other than what the definition takes"
    end.

  Definition by_name_10 (sc : scope) : D :=
    on_1 <~ Staged.get_field T (Staged.found sc "this:frflow.project.effects.samples.Bank") "from" ;;
    Staged.call_method T (Member "frflow.project.effects.samples.Account" "withdraw" "scala.Int:scala.Boolean") on_1 [(Staged.found sc "step#6")].

  Definition init_Cell_new_12 (this : val) (args : list val) : D :=
    sc <~ Staged.captured T this ;;
    match args with
    | [start_1] =>
        _ <~ Staged.set_field T this "start" start_1 ;;
        held_2 <~ Staged.get_field T this "start" ;;
        _ <~ Staged.set_field T this "held" held_2 ;;
        Staged.give VUnit
    | _ =>
        stuck "a call given other than what the definition takes"
    end.

  Definition m_Cell_held___13 (this : val) (args : list val) : D :=
    sc <~ Staged.captured T this ;;
    match args with
    | [x_1_1] =>
        Staged.give VUnit
    | _ =>
        stuck "a call given other than what the definition takes"
    end.

  Definition m_Cell_eq_14 (this : val) (args : list val) : D :=
    sc <~ Staged.captured T this ;;
    match args with
    | [other_1] =>
        on_2 <~ Staged.get_field T this "held" ;;
        arg_3 <~ Staged.get_field T other_1 "held" ;;
        Staged.out T (Member "scala.Int" "==" "scala.Int:scala.Boolean") on_2 [] [arg_3]
    | _ =>
        stuck "a call given other than what the definition takes"
    end.

  Definition m_Cell_ne_15 (this : val) (args : list val) : D :=
    sc <~ Staged.captured T this ;;
    match args with
    | [other_1] =>
        Staged.give (VBool false)
    | _ =>
        stuck "a call given other than what the definition takes"
    end.

  Definition m_Cell_add_16 (this : val) (args : list val) : D :=
    sc <~ Staged.captured T this ;;
    match args with
    | [n_1] =>
        _ <~ (value_3 <~ (on_2 <~ Staged.get_field T this "held" ;;
              Staged.out T (Member "scala.Int" "+" "scala.Int:scala.Int") on_2 [] [n_1]) ;;
           Staged.set_field T this "held" value_3) ;;
        Staged.get_field T this "held"
    | _ =>
        stuck "a call given other than what the definition takes"
    end.

  Definition m_Cell_add_17 (this : val) (args : list val) : D :=
    sc <~ Staged.captured T this ;;
    match args with
    | [n_1; times_2] =>
        left_3 <~ Staged.new_var T "<var>:scala.Int" times_2 ;;
        _ <~ (Staged.while_ T
             (on_4 <~ Staged.held T left_3 ;;
              Staged.out T (Member "scala.Int" ">" "scala.Int:scala.Boolean") on_4 [] [(vint (0)%Z)])
             (_ <~ (value_6 <~ (on_5 <~ Staged.get_field T this "held" ;;
                    Staged.out T (Member "scala.Int" "+" "scala.Int:scala.Int") on_5 [] [n_1]) ;;
                 Staged.set_field T this "held" value_6) ;;
              value_8 <~ (on_7 <~ Staged.held T left_3 ;;
                 Staged.out T (Member "scala.Int" "-" "scala.Int:scala.Int") on_7 [] [(vint (1)%Z)]) ;;
              Staged.set_var T left_3 value_8)) ;;
        Staged.get_field T this "held"
    | _ =>
        stuck "a call given other than what the definition takes"
    end.

  Definition init_Counter_new_18 (this : val) (args : list val) : D :=
    sc <~ Staged.captured T this ;;
    match args with
    | [start_1] =>
        _ <~ Staged.set_field T this "start" start_1 ;;
        count_2 <~ Staged.get_field T this "start" ;;
        _ <~ Staged.set_field T this "count" count_2 ;;
        Staged.give VUnit
    | _ =>
        stuck "a call given other than what the definition takes"
    end.

  Definition m_Counter_increment_19 (this : val) (args : list val) : D :=
    sc <~ Staged.captured T this ;;
    match args with
    | [by_1] =>
        _ <~ (value_3 <~ (on_2 <~ Staged.get_field T this "count" ;;
              Staged.out T (Member "scala.Int" "+" "scala.Int:scala.Int") on_2 [] [by_1]) ;;
           Staged.set_field T this "count" value_3) ;;
        Staged.get_field T this "count"
    | _ =>
        stuck "a call given other than what the definition takes"
    end.

  Definition m_Counter_current_20 (this : val) (args : list val) : D :=
    sc <~ Staged.captured T this ;;
    match args with
    | [] =>
        Staged.get_field T this "count"
    | _ =>
        stuck "a call given other than what the definition takes"
    end.

  Definition m_Counter_sumTo_21 (this : val) (args : list val) : D :=
    sc <~ Staged.captured T this ;;
    match args with
    | [n_1] =>
        i_2 <~ Staged.new_var T "<var>:scala.Int" (vint (0)%Z) ;;
        s_3 <~ Staged.new_var T "<var>:scala.Int" (vint (0)%Z) ;;
        _ <~ (Staged.while_ T
             (on_4 <~ Staged.held T i_2 ;;
              Staged.out T (Member "scala.Int" "<" "scala.Int:scala.Boolean") on_4 [] [n_1])
             (_ <~ (value_7 <~ (on_5 <~ Staged.held T s_3 ;;
                    arg_6 <~ Staged.held T i_2 ;;
                    Staged.out T (Member "scala.Int" "+" "scala.Int:scala.Int") on_5 [] [arg_6]) ;;
                 Staged.set_var T s_3 value_7) ;;
              value_9 <~ (on_8 <~ Staged.held T i_2 ;;
                 Staged.out T (Member "scala.Int" "+" "scala.Int:scala.Int") on_8 [] [(vint (1)%Z)]) ;;
              Staged.set_var T i_2 value_9)) ;;
        Staged.held T s_3
    | _ =>
        stuck "a call given other than what the definition takes"
    end.

  Definition init_Edges_new_22 (this : val) (args : list val) : D :=
    sc <~ Staged.captured T this ;;
    match args with
    | [] =>
        first_4 <~ (on_3 <~ Staged.get_field T this "second" ;;
           Staged.out T (Member "scala.Int" "+" "scala.Int:scala.Int") on_3 [] [(vint (1)%Z)]) ;;
        _ <~ Staged.set_field T this "first" first_4 ;;
        _ <~ Staged.set_field T this "second" (vint (5)%Z) ;;
        early_2 <~ (on_1 <~ Staged.get_field T this "late" ;;
           Staged.out T (Member "scala.Int" "+" "scala.Int:scala.Int") on_1 [] [(vint (1)%Z)]) ;;
        _ <~ Staged.set_field T this "early" early_2 ;;
        _ <~ Staged.set_field T this "late" (vint (7)%Z) ;;
        _ <~ Staged.set_field T this "log" (vint (0)%Z) ;;
        Staged.give VUnit
    | _ =>
        stuck "a call given other than what the definition takes"
    end.

  Definition m_Edges_keep_23 (this : val) (args : list val) : D :=
    sc <~ Staged.captured T this ;;
    match args with
    | [c_1; mark_2] =>
        _ <~ Staged.set_field T c_1 "held" mark_2 ;;
        Staged.give c_1
    | _ =>
        stuck "a call given other than what the definition takes"
    end.

  Definition m_Edges_receiver_24 (this : val) (args : list val) : D :=
    sc <~ Staged.captured T this ;;
    match args with
    | [] =>
        c_1 <~ Staged.construct_ T "frflow.project.effects.samples.Cell" [] [(vint (0)%Z)] ;;
        i_2 <~ Staged.new_var T "<var>:scala.Int" (vint (1)%Z) ;;
        _ <~ (test_4 <~ (on_3 <~ Staged.get_field T c_1 "held" ;;
              Staged.out T (Member "scala.Int" "==" "scala.Int:scala.Boolean") on_3 [] [(vint (0)%Z)]) ;;
           match test_4 with
           | VBool true =>
               on_6 <~ (arg_5 <~ (_ <~ Staged.set_var T i_2 (vint (5)%Z) ;;
                     Staged.held T i_2) ;;
                  Staged.call_method T (Member "frflow.project.effects.samples.Edges" "keep" "frflow.project.effects.samples.Cell,scala.Int:frflow.project.effects.samples.Cell") this [c_1; arg_5]) ;;
               Staged.set_field T on_6 "held" (vint (2)%Z)
           | VBool false =>
               Staged.give VUnit
           | _ =>
               stuck "a condition that gave no truth value"
           end) ;;
        on_7 <~ Staged.held T i_2 ;;
        arg_9 <~ (on_8 <~ Staged.get_field T c_1 "held" ;;
           Staged.out T (Member "scala.Int" "*" "scala.Int:scala.Int") on_8 [] [(vint (10)%Z)]) ;;
        Staged.out T (Member "scala.Int" "+" "scala.Int:scala.Int") on_7 [] [arg_9]
    | _ =>
        stuck "a call given other than what the definition takes"
    end.

  Definition m_Edges_looping_25 (this : val) (args : list val) : D :=
    sc <~ Staged.captured T this ;;
    match args with
    | [] =>
        c_1 <~ Staged.construct_ T "frflow.project.effects.samples.Cell" [] [(vint (0)%Z)] ;;
        i_2 <~ Staged.new_var T "<var>:scala.Int" (vint (0)%Z) ;;
        _ <~ (Staged.while_ T
             (on_3 <~ Staged.held T i_2 ;;
              Staged.out T (Member "scala.Int" "<" "scala.Int:scala.Boolean") on_3 [] [(vint (3)%Z)])
             (on_7 <~ (arg_6 <~ (_ <~ (value_5 <~ (on_4 <~ Staged.held T i_2 ;;
                          Staged.out T (Member "scala.Int" "+" "scala.Int:scala.Int") on_4 [] [(vint (1)%Z)]) ;;
                       Staged.set_var T i_2 value_5) ;;
                    Staged.held T i_2) ;;
                 Staged.call_method T (Member "frflow.project.effects.samples.Edges" "keep" "frflow.project.effects.samples.Cell,scala.Int:frflow.project.effects.samples.Cell") this [c_1; arg_6]) ;;
              value_8 <~ Staged.held T i_2 ;;
              Staged.set_field T on_7 "held" value_8)) ;;
        on_10 <~ (on_9 <~ Staged.held T i_2 ;;
           Staged.out T (Member "scala.Int" "*" "scala.Int:scala.Int") on_9 [] [(vint (10)%Z)]) ;;
        arg_11 <~ Staged.get_field T c_1 "held" ;;
        Staged.out T (Member "scala.Int" "+" "scala.Int:scala.Int") on_10 [] [arg_11]
    | _ =>
        stuck "a call given other than what the definition takes"
    end.

  Definition m_Edges_cells_26 (this : val) (args : list val) : D :=
    sc <~ Staged.captured T this ;;
    match args with
    | [] =>
        a_1 <~ Staged.construct_ T "frflow.project.effects.samples.Cell" [] [(vint (1)%Z)] ;;
        b_2 <~ Staged.construct_ T "frflow.project.effects.samples.Cell" [] [(vint (1)%Z)] ;;
        _ <~ Staged.set_field T a_1 "held" (vint (7)%Z) ;;
        _ <~ Staged.set_field T b_2 "held" (vint (7)%Z) ;;
        on_7 <~ (on_4 <~ (test_3 <~ Staged.call_method T (Member "frflow.project.effects.samples.Cell" "eq" "frflow.project.effects.samples.Cell:scala.Boolean") a_1 [b_2] ;;
              match test_3 with
              | VBool true =>
                  Staged.give (vint (1)%Z)
              | VBool false =>
                  Staged.give (vint (0)%Z)
              | _ =>
                  stuck "a condition that gave no truth value"
              end) ;;
           arg_6 <~ (test_5 <~ Staged.call_method T (Member "frflow.project.effects.samples.Cell" "ne" "frflow.project.effects.samples.Cell:scala.Boolean") a_1 [b_2] ;;
              match test_5 with
              | VBool true =>
                  Staged.give (vint (10)%Z)
              | VBool false =>
                  Staged.give (vint (0)%Z)
              | _ =>
                  stuck "a condition that gave no truth value"
              end) ;;
           Staged.out T (Member "scala.Int" "+" "scala.Int:scala.Int") on_4 [] [arg_6]) ;;
        arg_9 <~ (on_8 <~ Staged.get_field T a_1 "held" ;;
           Staged.out T (Member "scala.Int" "*" "scala.Int:scala.Int") on_8 [] [(vint (100)%Z)]) ;;
        Staged.out T (Member "scala.Int" "+" "scala.Int:scala.Int") on_7 [] [arg_9]
    | _ =>
        stuck "a call given other than what the definition takes"
    end.

  Definition m_Edges_overloads_27 (this : val) (args : list val) : D :=
    sc <~ Staged.captured T this ;;
    match args with
    | [] =>
        c_1 <~ Staged.construct_ T "frflow.project.effects.samples.Cell" [] [(vint (1)%Z)] ;;
        on_8 <~ (on_5 <~ (on_2 <~ Staged.call_method T (Member "frflow.project.effects.samples.Cell" "add" "scala.Int:scala.Int") c_1 [(vint (2)%Z)] ;;
              arg_4 <~ (on_3 <~ Staged.call_method T (Member "frflow.project.effects.samples.Cell" "add" "scala.Int,scala.Int:scala.Int") c_1 [(vint (3)%Z); (vint (4)%Z)] ;;
                 Staged.out T (Member "scala.Int" "*" "scala.Int:scala.Int") on_3 [] [(vint (100)%Z)]) ;;
              Staged.out T (Member "scala.Int" "+" "scala.Int:scala.Int") on_2 [] [arg_4]) ;;
           arg_7 <~ (on_6 <~ Staged.get_field T this "early" ;;
              Staged.out T (Member "scala.Int" "*" "scala.Int:scala.Int") on_6 [] [(vint (10000)%Z)]) ;;
           Staged.out T (Member "scala.Int" "+" "scala.Int:scala.Int") on_5 [] [arg_7]) ;;
        arg_10 <~ (on_9 <~ Staged.get_field T this "late" ;;
           Staged.out T (Member "scala.Int" "*" "scala.Int:scala.Int") on_9 [] [(vint (100000)%Z)]) ;;
        Staged.out T (Member "scala.Int" "+" "scala.Int:scala.Int") on_8 [] [arg_10]
    | _ =>
        stuck "a call given other than what the definition takes"
    end.

  Definition m_Edges_mark_28 (this : val) (args : list val) : D :=
    sc <~ Staged.captured T this ;;
    match args with
    | [d_1] =>
        _ <~ (value_4 <~ (on_3 <~ (on_2 <~ Staged.get_field T this "log" ;;
                 Staged.out T (Member "scala.Int" "*" "scala.Int:scala.Int") on_2 [] [(vint (10)%Z)]) ;;
              Staged.out T (Member "scala.Int" "+" "scala.Int:scala.Int") on_3 [] [d_1]) ;;
           Staged.set_field T this "log" value_4) ;;
        Staged.give d_1
    | _ =>
        stuck "a call given other than what the definition takes"
    end.

  Definition m_Edges_pick_29 (this : val) (args : list val) : D :=
    sc <~ Staged.captured T this ;;
    match args with
    | [c_1; d_2] =>
        _ <~ (value_5 <~ (on_4 <~ (on_3 <~ Staged.get_field T this "log" ;;
                 Staged.out T (Member "scala.Int" "*" "scala.Int:scala.Int") on_3 [] [(vint (10)%Z)]) ;;
              Staged.out T (Member "scala.Int" "+" "scala.Int:scala.Int") on_4 [] [d_2]) ;;
           Staged.set_field T this "log" value_5) ;;
        Staged.give c_1
    | _ =>
        stuck "a call given other than what the definition takes"
    end.

  Definition m_Edges_ordering_30 (this : val) (args : list val) : D :=
    sc <~ Staged.captured T this ;;
    match args with
    | [] =>
        c_2 <~ (arg_1 <~ Staged.call_method T (Member "frflow.project.effects.samples.Edges" "mark" "scala.Int:scala.Int") this [(vint (1)%Z)] ;;
           Staged.construct_ T "frflow.project.effects.samples.Cell" [] [arg_1]) ;;
        added_6 <~ (on_3 <~ Staged.call_method T (Member "frflow.project.effects.samples.Edges" "pick" "frflow.project.effects.samples.Cell,scala.Int:frflow.project.effects.samples.Cell") this [c_2; (vint (2)%Z)] ;;
           arg_4 <~ Staged.call_method T (Member "frflow.project.effects.samples.Edges" "mark" "scala.Int:scala.Int") this [(vint (3)%Z)] ;;
           arg_5 <~ Staged.call_method T (Member "frflow.project.effects.samples.Edges" "mark" "scala.Int:scala.Int") this [(vint (4)%Z)] ;;
           Staged.call_method T (Member "frflow.project.effects.samples.Cell" "add" "scala.Int,scala.Int:scala.Int") on_3 [arg_4; arg_5]) ;;
        _ <~ (value_11 <~ (on_7 <~ Staged.call_method T (Member "frflow.project.effects.samples.Edges" "mark" "scala.Int:scala.Int") this [(vint (5)%Z)] ;;
              arg_10 <~ (on_8 <~ Staged.call_method T (Member "frflow.project.effects.samples.Edges" "mark" "scala.Int:scala.Int") this [(vint (6)%Z)] ;;
                 arg_9 <~ Staged.call_method T (Member "frflow.project.effects.samples.Edges" "mark" "scala.Int:scala.Int") this [(vint (7)%Z)] ;;
                 Staged.out T (Member "scala.Int" "*" "scala.Int:scala.Int") on_8 [] [arg_9]) ;;
              Staged.out T (Member "scala.Int" "+" "scala.Int:scala.Int") on_7 [] [arg_10]) ;;
           Staged.set_field T c_2 "held" value_11) ;;
        test_12 <~ Staged.out T (Member "scala.Int" ">" "scala.Int:scala.Boolean") added_6 [] [(vint (0)%Z)] ;;
        match test_12 with
        | VBool true =>
            Staged.get_field T this "log"
        | VBool false =>
            Staged.give (vint (0)%Z)
        | _ =>
            stuck "a condition that gave no truth value"
        end
    | _ =>
        stuck "a call given other than what the definition takes"
    end.

  Definition init_Numbers_new_31 (this : val) (args : list val) : D :=
    sc <~ Staged.captured T this ;;
    match args with
    | [] =>
        Staged.give VUnit
    | _ =>
        stuck "a call given other than what the definition takes"
    end.

  Definition m_Numbers_largest_32 (this : val) (args : list val) : D :=
    sc <~ Staged.captured T this ;;
    match args with
    | [a_1; b_2; c_3] =>
        best_4 <~ Staged.new_var T "<var>:scala.Int" a_1 ;;
        _ <~ (test_6 <~ (arg_5 <~ Staged.held T best_4 ;;
              Staged.out T (Member "scala.Int" ">" "scala.Int:scala.Boolean") b_2 [] [arg_5]) ;;
           match test_6 with
           | VBool true =>
               Staged.set_var T best_4 b_2
           | VBool false =>
               Staged.give VUnit
           | _ =>
               stuck "a condition that gave no truth value"
           end) ;;
        _ <~ (test_8 <~ (arg_7 <~ Staged.held T best_4 ;;
              Staged.out T (Member "scala.Int" ">" "scala.Int:scala.Boolean") c_3 [] [arg_7]) ;;
           match test_8 with
           | VBool true =>
               Staged.set_var T best_4 c_3
           | VBool false =>
               Staged.give VUnit
           | _ =>
               stuck "a condition that gave no truth value"
           end) ;;
        Staged.held T best_4
    | _ =>
        stuck "a call given other than what the definition takes"
    end.

  Definition m_Numbers_power_33 (this : val) (args : list val) : D :=
    sc <~ Staged.captured T this ;;
    match args with
    | [base_1; n_2] =>
        result_3 <~ Staged.new_var T "<var>:scala.Int" (vint (1)%Z) ;;
        left_4 <~ Staged.new_var T "<var>:scala.Int" n_2 ;;
        _ <~ (Staged.while_ T
             (on_5 <~ Staged.held T left_4 ;;
              Staged.out T (Member "scala.Int" ">" "scala.Int:scala.Boolean") on_5 [] [(vint (0)%Z)])
             (_ <~ (value_7 <~ (on_6 <~ Staged.held T result_3 ;;
                    Staged.out T (Member "scala.Int" "*" "scala.Int:scala.Int") on_6 [] [base_1]) ;;
                 Staged.set_var T result_3 value_7) ;;
              value_9 <~ (on_8 <~ Staged.held T left_4 ;;
                 Staged.out T (Member "scala.Int" "-" "scala.Int:scala.Int") on_8 [] [(vint (1)%Z)]) ;;
              Staged.set_var T left_4 value_9)) ;;
        Staged.held T result_3
    | _ =>
        stuck "a call given other than what the definition takes"
    end.

  Definition m_Numbers_gcd_34 (this : val) (args : list val) : D :=
    sc <~ Staged.captured T this ;;
    match args with
    | [a_1; b_2] =>
        x_3 <~ Staged.new_var T "<var>:scala.Int" a_1 ;;
        y_4 <~ Staged.new_var T "<var>:scala.Int" b_2 ;;
        _ <~ (Staged.while_ T
             (on_5 <~ Staged.held T x_3 ;;
              arg_6 <~ Staged.held T y_4 ;;
              Staged.out T (Member "scala.Int" "!=" "scala.Int:scala.Boolean") on_5 [] [arg_6])
             (test_9 <~ (on_7 <~ Staged.held T x_3 ;;
                 arg_8 <~ Staged.held T y_4 ;;
                 Staged.out T (Member "scala.Int" ">" "scala.Int:scala.Boolean") on_7 [] [arg_8]) ;;
              match test_9 with
              | VBool true =>
                  value_12 <~ (on_10 <~ Staged.held T x_3 ;;
                     arg_11 <~ Staged.held T y_4 ;;
                     Staged.out T (Member "scala.Int" "-" "scala.Int:scala.Int") on_10 [] [arg_11]) ;;
                  Staged.set_var T x_3 value_12
              | VBool false =>
                  value_15 <~ (on_13 <~ Staged.held T y_4 ;;
                     arg_14 <~ Staged.held T x_3 ;;
                     Staged.out T (Member "scala.Int" "-" "scala.Int:scala.Int") on_13 [] [arg_14]) ;;
                  Staged.set_var T y_4 value_15
              | _ =>
                  stuck "a condition that gave no truth value"
              end)) ;;
        Staged.held T x_3
    | _ =>
        stuck "a call given other than what the definition takes"
    end.

  Definition m_Numbers_triangle_35 (this : val) (args : list val) : D :=
    sc <~ Staged.captured T this ;;
    match args with
    | [rows_1] =>
        total_2 <~ Staged.new_var T "<var>:scala.Int" (vint (0)%Z) ;;
        row_3 <~ Staged.new_var T "<var>:scala.Int" (vint (1)%Z) ;;
        _ <~ (Staged.while_ T
             (on_4 <~ Staged.held T row_3 ;;
              Staged.out T (Member "scala.Int" "<=" "scala.Int:scala.Boolean") on_4 [] [rows_1])
             (column_5 <~ Staged.new_var T "<var>:scala.Int" (vint (0)%Z) ;;
              _ <~ (Staged.while_ T
                   (on_6 <~ Staged.held T column_5 ;;
                    arg_7 <~ Staged.held T row_3 ;;
                    Staged.out T (Member "scala.Int" "<" "scala.Int:scala.Boolean") on_6 [] [arg_7])
                   (_ <~ (value_9 <~ (on_8 <~ Staged.held T total_2 ;;
                          Staged.out T (Member "scala.Int" "+" "scala.Int:scala.Int") on_8 [] [(vint (1)%Z)]) ;;
                       Staged.set_var T total_2 value_9) ;;
                    value_11 <~ (on_10 <~ Staged.held T column_5 ;;
                       Staged.out T (Member "scala.Int" "+" "scala.Int:scala.Int") on_10 [] [(vint (1)%Z)]) ;;
                    Staged.set_var T column_5 value_11)) ;;
              value_13 <~ (on_12 <~ Staged.held T row_3 ;;
                 Staged.out T (Member "scala.Int" "+" "scala.Int:scala.Int") on_12 [] [(vint (1)%Z)]) ;;
              Staged.set_var T row_3 value_13)) ;;
        Staged.held T total_2
    | _ =>
        stuck "a call given other than what the definition takes"
    end.

  Definition m_Numbers_signOf_36 (this : val) (args : list val) : D :=
    sc <~ Staged.captured T this ;;
    match args with
    | [n_1] =>
        test_2 <~ Staged.out T (Member "scala.Int" "<" "scala.Int:scala.Boolean") n_1 [] [(vint (0)%Z)] ;;
        match test_2 with
        | VBool true =>
            Staged.give (vint (-1)%Z)
        | VBool false =>
            test_3 <~ Staged.out T (Member "scala.Int" "==" "scala.Int:scala.Boolean") n_1 [] [(vint (0)%Z)] ;;
            match test_3 with
            | VBool true =>
                Staged.give (vint (0)%Z)
            | VBool false =>
                Staged.give (vint (1)%Z)
            | _ =>
                stuck "a condition that gave no truth value"
            end
        | _ =>
            stuck "a condition that gave no truth value"
        end
    | _ =>
        stuck "a call given other than what the definition takes"
    end.

  Definition m_Numbers_either_40 (this : val) (args : list val) : D :=
    sc <~ Staged.captured T this ;;
    match args with
    | [a_1; b_2] =>
        on_3 <~ (Staged.out_lazy T (Member "scala.Boolean" "||" "scala.Boolean:scala.Boolean") a_1 []
             [
               inl (VCode (Thunk (Ident (Local "<by-name>" 37)) ([("a#17", a_1); ("b#18", b_2); ("this:frflow.project.effects.samples.Numbers", this); ("this:java.lang.Object", this)] ++ sc)%list))
             ]) ;;
        Staged.out_lazy T (Member "scala.Boolean" "&&" "scala.Boolean:scala.Boolean") on_3 []
          [
            inl (VCode (Thunk (Ident (Local "<by-name>" 38)) ([("a#17", a_1); ("b#18", b_2); ("this:frflow.project.effects.samples.Numbers", this); ("this:java.lang.Object", this)] ++ sc)%list))
          ]
    | _ =>
        stuck "a call given other than what the definition takes"
    end.

  Definition by_name_37 (sc : scope) : D :=
    Staged.give (Staged.found sc "b#18").

  Definition by_name_39 (sc : scope) : D :=
    Staged.give (Staged.found sc "b#18").

  Definition by_name_38 (sc : scope) : D :=
    on_1 <~ (Staged.out_lazy T (Member "scala.Boolean" "&&" "scala.Boolean:scala.Boolean") (Staged.found sc "a#17") []
         [
           inl (VCode (Thunk (Ident (Local "<by-name>" 39)) sc))
         ]) ;;
    Staged.out T (Member "scala.Boolean" "unary_!" ":scala.Boolean") on_1 [] [].

  Definition init_Pair_new_41 (this : val) (args : list val) : D :=
    sc <~ Staged.captured T this ;;
    match args with
    | [left_1; right_2] =>
        _ <~ Staged.set_field T this "left" left_1 ;;
        _ <~ Staged.set_field T this "right" right_2 ;;
        Staged.give VUnit
    | _ =>
        stuck "a call given other than what the definition takes"
    end.

  Definition m_Pair_bump_42 (this : val) (args : list val) : D :=
    sc <~ Staged.captured T this ;;
    match args with
    | [] =>
        on_2 <~ (on_1 <~ Staged.get_field T this "left" ;;
           Staged.call_method T (Member "frflow.project.effects.samples.Counter" "increment" "scala.Int:scala.Int") on_1 [(vint (1)%Z)]) ;;
        arg_4 <~ (on_3 <~ Staged.get_field T this "right" ;;
           Staged.call_method T (Member "frflow.project.effects.samples.Counter" "increment" "scala.Int:scala.Int") on_3 [(vint (2)%Z)]) ;;
        Staged.out T (Member "scala.Int" "+" "scala.Int:scala.Int") on_2 [] [arg_4]
    | _ =>
        stuck "a call given other than what the definition takes"
    end.

  Definition m_Pair_same_43 (this : val) (args : list val) : D :=
    sc <~ Staged.captured T this ;;
    match args with
    | [] =>
        left_1 <~ Staged.get_field T this "left" ;;
        arg_2 <~ Staged.get_field T this "right" ;;
        Staged.same_ T left_1 arg_2
    | _ =>
        stuck "a call given other than what the definition takes"
    end.

  Definition init_Scenarios_new_44 (this : val) (args : list val) : D :=
    sc <~ Staged.captured T this ;;
    match args with
    | [] =>
        Staged.give VUnit
    | _ =>
        stuck "a call given other than what the definition takes"
    end.

  Definition m_Scenarios_counters_45 (this : val) (args : list val) : D :=
    sc <~ Staged.captured T this ;;
    match args with
    | [] =>
        pair_3 <~ (arg_1 <~ Staged.construct_ T "frflow.project.effects.samples.Counter" [] [(vint (10)%Z)] ;;
           arg_2 <~ Staged.construct_ T "frflow.project.effects.samples.Counter" [] [(vint (20)%Z)] ;;
           Staged.construct_ T "frflow.project.effects.samples.Pair" [] [arg_1; arg_2]) ;;
        on_7 <~ (on_4 <~ Staged.call_method T (Member "frflow.project.effects.samples.Pair" "bump" ":scala.Int") pair_3 [] ;;
           arg_6 <~ (on_5 <~ Staged.get_field T pair_3 "left" ;;
              Staged.call_method T (Member "frflow.project.effects.samples.Counter" "sumTo" "scala.Int:scala.Int") on_5 [(vint (5)%Z)]) ;;
           Staged.out T (Member "scala.Int" "+" "scala.Int:scala.Int") on_4 [] [arg_6]) ;;
        arg_9 <~ (on_8 <~ Staged.get_field T pair_3 "right" ;;
           Staged.call_method T (Member "frflow.project.effects.samples.Counter" "current" ":scala.Int") on_8 []) ;;
        Staged.out T (Member "scala.Int" "+" "scala.Int:scala.Int") on_7 [] [arg_9]
    | _ =>
        stuck "a call given other than what the definition takes"
    end.

  Definition m_Scenarios_sharing_46 (this : val) (args : list val) : D :=
    sc <~ Staged.captured T this ;;
    match args with
    | [] =>
        one_1 <~ Staged.construct_ T "frflow.project.effects.samples.Counter" [] [(vint (1)%Z)] ;;
        pair_2 <~ Staged.construct_ T "frflow.project.effects.samples.Pair" [] [one_1; one_1] ;;
        bumped_3 <~ Staged.call_method T (Member "frflow.project.effects.samples.Pair" "bump" ":scala.Int") pair_2 [] ;;
        test_4 <~ Staged.call_method T (Member "frflow.project.effects.samples.Pair" "same" ":scala.Boolean") pair_2 [] ;;
        match test_4 with
        | VBool true =>
            arg_5 <~ Staged.call_method T (Member "frflow.project.effects.samples.Counter" "current" ":scala.Int") one_1 [] ;;
            Staged.out T (Member "scala.Int" "+" "scala.Int:scala.Int") bumped_3 [] [arg_5]
        | VBool false =>
            Staged.give (vint (0)%Z)
        | _ =>
            stuck "a condition that gave no truth value"
        end
    | _ =>
        stuck "a call given other than what the definition takes"
    end.

  Definition m_Scenarios_banking_47 (this : val) (args : list val) : D :=
    sc <~ Staged.captured T this ;;
    match args with
    | [] =>
        a_1 <~ Staged.construct_ T "frflow.project.effects.samples.Account" [] [(vint (100)%Z)] ;;
        b_2 <~ Staged.construct_ T "frflow.project.effects.samples.Account" [] [(vint (5)%Z)] ;;
        bank_3 <~ Staged.construct_ T "frflow.project.effects.samples.Bank" [] [a_1; b_2] ;;
        moved_5 <~ (test_4 <~ Staged.call_method T (Member "frflow.project.effects.samples.Bank" "transfer" "scala.Int:scala.Boolean") bank_3 [(vint (30)%Z)] ;;
           match test_4 with
           | VBool true =>
               Staged.give (vint (1)%Z)
           | VBool false =>
               Staged.give (vint (0)%Z)
           | _ =>
               stuck "a condition that gave no truth value"
           end) ;;
        again_7 <~ (test_6 <~ Staged.call_method T (Member "frflow.project.effects.samples.Bank" "transfer" "scala.Int:scala.Boolean") bank_3 [(vint (500)%Z)] ;;
           match test_6 with
           | VBool true =>
               Staged.give (vint (1)%Z)
           | VBool false =>
               Staged.give (vint (0)%Z)
           | _ =>
               stuck "a condition that gave no truth value"
           end) ;;
        on_15 <~ (on_12 <~ (on_9 <~ (arg_8 <~ Staged.out T (Member "scala.Int" "*" "scala.Int:scala.Int") again_7 [] [(vint (10)%Z)] ;;
                 Staged.out T (Member "scala.Int" "+" "scala.Int:scala.Int") moved_5 [] [arg_8]) ;;
              arg_11 <~ (on_10 <~ Staged.call_method T (Member "frflow.project.effects.samples.Account" "total" ":scala.Int") a_1 [] ;;
                 Staged.out T (Member "scala.Int" "*" "scala.Int:scala.Int") on_10 [] [(vint (100)%Z)]) ;;
              Staged.out T (Member "scala.Int" "+" "scala.Int:scala.Int") on_9 [] [arg_11]) ;;
           arg_14 <~ (on_13 <~ Staged.call_method T (Member "frflow.project.effects.samples.Account" "total" ":scala.Int") b_2 [] ;;
              Staged.out T (Member "scala.Int" "*" "scala.Int:scala.Int") on_13 [] [(vint (10000)%Z)]) ;;
           Staged.out T (Member "scala.Int" "+" "scala.Int:scala.Int") on_12 [] [arg_14]) ;;
        arg_17 <~ (on_16 <~ Staged.call_method T (Member "frflow.project.effects.samples.Account" "refusals" ":scala.Int") a_1 [] ;;
           Staged.out T (Member "scala.Int" "*" "scala.Int:scala.Int") on_16 [] [(vint (1000000)%Z)]) ;;
        Staged.out T (Member "scala.Int" "+" "scala.Int:scala.Int") on_15 [] [arg_17]
    | _ =>
        stuck "a call given other than what the definition takes"
    end.

  Definition m_Scenarios_draining_48 (this : val) (args : list val) : D :=
    sc <~ Staged.captured T this ;;
    match args with
    | [] =>
        a_1 <~ Staged.construct_ T "frflow.project.effects.samples.Account" [] [(vint (50)%Z)] ;;
        b_2 <~ Staged.construct_ T "frflow.project.effects.samples.Account" [] [(vint (0)%Z)] ;;
        bank_3 <~ Staged.construct_ T "frflow.project.effects.samples.Bank" [] [a_1; b_2] ;;
        some_4 <~ Staged.call_method T (Member "frflow.project.effects.samples.Bank" "drainAtMost" "scala.Int,scala.Int:scala.Int") bank_3 [(vint (7)%Z); (vint (3)%Z)] ;;
        rest_5 <~ Staged.call_method T (Member "frflow.project.effects.samples.Bank" "drain" "scala.Int:scala.Int") bank_3 [(vint (7)%Z)] ;;
        on_13 <~ (on_10 <~ (on_7 <~ (arg_6 <~ Staged.out T (Member "scala.Int" "*" "scala.Int:scala.Int") rest_5 [] [(vint (100)%Z)] ;;
                 Staged.out T (Member "scala.Int" "+" "scala.Int:scala.Int") some_4 [] [arg_6]) ;;
              arg_9 <~ (on_8 <~ Staged.call_method T (Member "frflow.project.effects.samples.Account" "total" ":scala.Int") a_1 [] ;;
                 Staged.out T (Member "scala.Int" "*" "scala.Int:scala.Int") on_8 [] [(vint (10000)%Z)]) ;;
              Staged.out T (Member "scala.Int" "+" "scala.Int:scala.Int") on_7 [] [arg_9]) ;;
           arg_12 <~ (on_11 <~ Staged.call_method T (Member "frflow.project.effects.samples.Account" "total" ":scala.Int") b_2 [] ;;
              Staged.out T (Member "scala.Int" "*" "scala.Int:scala.Int") on_11 [] [(vint (100000)%Z)]) ;;
           Staged.out T (Member "scala.Int" "+" "scala.Int:scala.Int") on_10 [] [arg_12]) ;;
        arg_15 <~ (on_14 <~ Staged.call_method T (Member "frflow.project.effects.samples.Account" "refusals" ":scala.Int") a_1 [] ;;
           Staged.out T (Member "scala.Int" "*" "scala.Int:scala.Int") on_14 [] [(vint (10000000)%Z)]) ;;
        Staged.out T (Member "scala.Int" "+" "scala.Int:scala.Int") on_13 [] [arg_15]
    | _ =>
        stuck "a call given other than what the definition takes"
    end.

  Definition m_Scenarios_computing_50 (this : val) (args : list val) : D :=
    sc <~ Staged.captured T this ;;
    match args with
    | [] =>
        n_1 <~ Staged.construct_ T "frflow.project.effects.samples.Numbers" [] [] ;;
        truths_4 <~ (test_3 <~ (on_2 <~ Staged.call_method T (Member "frflow.project.effects.samples.Numbers" "either" "scala.Boolean,scala.Boolean:scala.Boolean") n_1 [(VBool true); (VBool false)] ;;
              Staged.out_lazy T (Member "scala.Boolean" "&&" "scala.Boolean:scala.Boolean") on_2 []
                [
                  inl (VCode (Thunk (Ident (Local "<by-name>" 49)) ([("n#14", n_1); ("this:frflow.project.effects.samples.Scenarios", this); ("this:java.lang.Object", this)] ++ sc)%list))
                ]) ;;
           match test_3 with
           | VBool true =>
               Staged.give (vint (1)%Z)
           | VBool false =>
               Staged.give (vint (0)%Z)
           | _ =>
               stuck "a condition that gave no truth value"
           end) ;;
        on_13 <~ (on_11 <~ (on_8 <~ (on_5 <~ Staged.call_method T (Member "frflow.project.effects.samples.Numbers" "largest" "scala.Int,scala.Int,scala.Int:scala.Int") n_1 [(vint (3)%Z); (vint (9)%Z); (vint (4)%Z)] ;;
                 arg_7 <~ (on_6 <~ Staged.call_method T (Member "frflow.project.effects.samples.Numbers" "gcd" "scala.Int,scala.Int:scala.Int") n_1 [(vint (84)%Z); (vint (36)%Z)] ;;
                    Staged.out T (Member "scala.Int" "*" "scala.Int:scala.Int") on_6 [] [(vint (10)%Z)]) ;;
                 Staged.out T (Member "scala.Int" "+" "scala.Int:scala.Int") on_5 [] [arg_7]) ;;
              arg_10 <~ (on_9 <~ Staged.call_method T (Member "frflow.project.effects.samples.Numbers" "triangle" "scala.Int:scala.Int") n_1 [(vint (6)%Z)] ;;
                 Staged.out T (Member "scala.Int" "*" "scala.Int:scala.Int") on_9 [] [(vint (1000)%Z)]) ;;
              Staged.out T (Member "scala.Int" "+" "scala.Int:scala.Int") on_8 [] [arg_10]) ;;
           arg_12 <~ Staged.call_method T (Member "frflow.project.effects.samples.Numbers" "signOf" "scala.Int:scala.Int") n_1 [(vint (-5)%Z)] ;;
           Staged.out T (Member "scala.Int" "+" "scala.Int:scala.Int") on_11 [] [arg_12]) ;;
        arg_14 <~ Staged.out T (Member "scala.Int" "*" "scala.Int:scala.Int") truths_4 [] [(vint (100000)%Z)] ;;
        Staged.out T (Member "scala.Int" "+" "scala.Int:scala.Int") on_13 [] [arg_14]
    | _ =>
        stuck "a call given other than what the definition takes"
    end.

  Definition by_name_49 (sc : scope) : D :=
    on_1 <~ Staged.call_method T (Member "frflow.project.effects.samples.Numbers" "either" "scala.Boolean,scala.Boolean:scala.Boolean") (Staged.found sc "n#14") [(VBool true); (VBool true)] ;;
    Staged.out T (Member "scala.Boolean" "unary_!" ":scala.Boolean") on_1 [] [].

  Definition m_Scenarios_wrapping_51 (this : val) (args : list val) : D :=
    sc <~ Staged.captured T this ;;
    match args with
    | [] =>
        n_1 <~ Staged.construct_ T "frflow.project.effects.samples.Numbers" [] [] ;;
        on_2 <~ Staged.call_method T (Member "frflow.project.effects.samples.Numbers" "power" "scala.Int,scala.Int:scala.Int") n_1 [(vint (7)%Z); (vint (20)%Z)] ;;
        arg_3 <~ Staged.call_method T (Member "frflow.project.effects.samples.Numbers" "power" "scala.Int,scala.Int:scala.Int") n_1 [(vint (-3)%Z); (vint (31)%Z)] ;;
        Staged.out T (Member "scala.Int" "+" "scala.Int:scala.Int") on_2 [] [arg_3]
    | _ =>
        stuck "a call given other than what the definition takes"
    end.

  Definition m_Scenarios_edges_52 (this : val) (args : list val) : D :=
    sc <~ Staged.captured T this ;;
    match args with
    | [] =>
        e_1 <~ Staged.construct_ T "frflow.project.effects.samples.Edges" [] [] ;;
        on_8 <~ (on_5 <~ (on_2 <~ Staged.get_field T e_1 "first" ;;
              arg_4 <~ (on_3 <~ Staged.call_method T (Member "frflow.project.effects.samples.Edges" "receiver" ":scala.Int") e_1 [] ;;
                 Staged.out T (Member "scala.Int" "*" "scala.Int:scala.Int") on_3 [] [(vint (10)%Z)]) ;;
              Staged.out T (Member "scala.Int" "+" "scala.Int:scala.Int") on_2 [] [arg_4]) ;;
           arg_7 <~ (on_6 <~ Staged.call_method T (Member "frflow.project.effects.samples.Edges" "looping" ":scala.Int") e_1 [] ;;
              Staged.out T (Member "scala.Int" "*" "scala.Int:scala.Int") on_6 [] [(vint (1000)%Z)]) ;;
           Staged.out T (Member "scala.Int" "+" "scala.Int:scala.Int") on_5 [] [arg_7]) ;;
        arg_10 <~ (on_9 <~ Staged.call_method T (Member "frflow.project.effects.samples.Edges" "cells" ":scala.Int") e_1 [] ;;
           Staged.out T (Member "scala.Int" "*" "scala.Int:scala.Int") on_9 [] [(vint (100000)%Z)]) ;;
        Staged.out T (Member "scala.Int" "+" "scala.Int:scala.Int") on_8 [] [arg_10]
    | _ =>
        stuck "a call given other than what the definition takes"
    end.

  Definition m_Scenarios_naming_53 (this : val) (args : list val) : D :=
    sc <~ Staged.captured T this ;;
    match args with
    | [] =>
        on_1 <~ Staged.construct_ T "frflow.project.effects.samples.Edges" [] [] ;;
        Staged.call_method T (Member "frflow.project.effects.samples.Edges" "overloads" ":scala.Int") on_1 []
    | _ =>
        stuck "a call given other than what the definition takes"
    end.

  Definition m_Scenarios_ordering_54 (this : val) (args : list val) : D :=
    sc <~ Staged.captured T this ;;
    match args with
    | [] =>
        on_1 <~ Staged.construct_ T "frflow.project.effects.samples.Edges" [] [] ;;
        Staged.call_method T (Member "frflow.project.effects.samples.Edges" "ordering" ":scala.Int") on_1 []
    | _ =>
        stuck "a call given other than what the definition takes"
    end.

  Definition Code_units : Staged.units := Staged.Units
    (fun s =>
      if sym_eqb s (Member "frflow.project.effects.samples.Account" "withdraw" "scala.Int:scala.Boolean") then Some m_Account_withdraw_3 else
      if sym_eqb s (Member "frflow.project.effects.samples.Account" "deposit" "scala.Int:scala.Unit") then Some m_Account_deposit_4 else
      if sym_eqb s (Member "frflow.project.effects.samples.Account" "total" ":scala.Int") then Some m_Account_total_5 else
      if sym_eqb s (Member "frflow.project.effects.samples.Account" "refusals" ":scala.Int") then Some m_Account_refusals_6 else
      if sym_eqb s (Member "frflow.project.effects.samples.Bank" "transfer" "scala.Int:scala.Boolean") then Some m_Bank_transfer_8 else
      if sym_eqb s (Member "frflow.project.effects.samples.Bank" "drain" "scala.Int:scala.Int") then Some m_Bank_drain_9 else
      if sym_eqb s (Member "frflow.project.effects.samples.Bank" "drainAtMost" "scala.Int,scala.Int:scala.Int") then Some m_Bank_drainAtMost_11 else
      if sym_eqb s (Member "frflow.project.effects.samples.Cell" "held_=" "scala.Int:scala.Unit") then Some m_Cell_held___13 else
      if sym_eqb s (Member "frflow.project.effects.samples.Cell" "eq" "frflow.project.effects.samples.Cell:scala.Boolean") then Some m_Cell_eq_14 else
      if sym_eqb s (Member "frflow.project.effects.samples.Cell" "ne" "frflow.project.effects.samples.Cell:scala.Boolean") then Some m_Cell_ne_15 else
      if sym_eqb s (Member "frflow.project.effects.samples.Cell" "add" "scala.Int:scala.Int") then Some m_Cell_add_16 else
      if sym_eqb s (Member "frflow.project.effects.samples.Cell" "add" "scala.Int,scala.Int:scala.Int") then Some m_Cell_add_17 else
      if sym_eqb s (Member "frflow.project.effects.samples.Counter" "increment" "scala.Int:scala.Int") then Some m_Counter_increment_19 else
      if sym_eqb s (Member "frflow.project.effects.samples.Counter" "current" ":scala.Int") then Some m_Counter_current_20 else
      if sym_eqb s (Member "frflow.project.effects.samples.Counter" "sumTo" "scala.Int:scala.Int") then Some m_Counter_sumTo_21 else
      if sym_eqb s (Member "frflow.project.effects.samples.Edges" "keep" "frflow.project.effects.samples.Cell,scala.Int:frflow.project.effects.samples.Cell") then Some m_Edges_keep_23 else
      if sym_eqb s (Member "frflow.project.effects.samples.Edges" "receiver" ":scala.Int") then Some m_Edges_receiver_24 else
      if sym_eqb s (Member "frflow.project.effects.samples.Edges" "looping" ":scala.Int") then Some m_Edges_looping_25 else
      if sym_eqb s (Member "frflow.project.effects.samples.Edges" "cells" ":scala.Int") then Some m_Edges_cells_26 else
      if sym_eqb s (Member "frflow.project.effects.samples.Edges" "overloads" ":scala.Int") then Some m_Edges_overloads_27 else
      if sym_eqb s (Member "frflow.project.effects.samples.Edges" "mark" "scala.Int:scala.Int") then Some m_Edges_mark_28 else
      if sym_eqb s (Member "frflow.project.effects.samples.Edges" "pick" "frflow.project.effects.samples.Cell,scala.Int:frflow.project.effects.samples.Cell") then Some m_Edges_pick_29 else
      if sym_eqb s (Member "frflow.project.effects.samples.Edges" "ordering" ":scala.Int") then Some m_Edges_ordering_30 else
      if sym_eqb s (Member "frflow.project.effects.samples.Numbers" "largest" "scala.Int,scala.Int,scala.Int:scala.Int") then Some m_Numbers_largest_32 else
      if sym_eqb s (Member "frflow.project.effects.samples.Numbers" "power" "scala.Int,scala.Int:scala.Int") then Some m_Numbers_power_33 else
      if sym_eqb s (Member "frflow.project.effects.samples.Numbers" "gcd" "scala.Int,scala.Int:scala.Int") then Some m_Numbers_gcd_34 else
      if sym_eqb s (Member "frflow.project.effects.samples.Numbers" "triangle" "scala.Int:scala.Int") then Some m_Numbers_triangle_35 else
      if sym_eqb s (Member "frflow.project.effects.samples.Numbers" "signOf" "scala.Int:scala.Int") then Some m_Numbers_signOf_36 else
      if sym_eqb s (Member "frflow.project.effects.samples.Numbers" "either" "scala.Boolean,scala.Boolean:scala.Boolean") then Some m_Numbers_either_40 else
      if sym_eqb s (Member "frflow.project.effects.samples.Pair" "bump" ":scala.Int") then Some m_Pair_bump_42 else
      if sym_eqb s (Member "frflow.project.effects.samples.Pair" "same" ":scala.Boolean") then Some m_Pair_same_43 else
      if sym_eqb s (Member "frflow.project.effects.samples.Scenarios" "counters" ":scala.Int") then Some m_Scenarios_counters_45 else
      if sym_eqb s (Member "frflow.project.effects.samples.Scenarios" "sharing" ":scala.Int") then Some m_Scenarios_sharing_46 else
      if sym_eqb s (Member "frflow.project.effects.samples.Scenarios" "banking" ":scala.Int") then Some m_Scenarios_banking_47 else
      if sym_eqb s (Member "frflow.project.effects.samples.Scenarios" "draining" ":scala.Int") then Some m_Scenarios_draining_48 else
      if sym_eqb s (Member "frflow.project.effects.samples.Scenarios" "computing" ":scala.Int") then Some m_Scenarios_computing_50 else
      if sym_eqb s (Member "frflow.project.effects.samples.Scenarios" "wrapping" ":scala.Int") then Some m_Scenarios_wrapping_51 else
      if sym_eqb s (Member "frflow.project.effects.samples.Scenarios" "edges" ":scala.Int") then Some m_Scenarios_edges_52 else
      if sym_eqb s (Member "frflow.project.effects.samples.Scenarios" "naming" ":scala.Int") then Some m_Scenarios_naming_53 else
      if sym_eqb s (Member "frflow.project.effects.samples.Scenarios" "ordering" ":scala.Int") then Some m_Scenarios_ordering_54 else
      None)
    (fun cls =>
      if String.eqb cls "frflow.project.effects.samples.Account" then Some init_Account_new_1 else
      if String.eqb cls "frflow.project.effects.samples.Bank" then Some init_Bank_new_7 else
      if String.eqb cls "frflow.project.effects.samples.Cell" then Some init_Cell_new_12 else
      if String.eqb cls "frflow.project.effects.samples.Counter" then Some init_Counter_new_18 else
      if String.eqb cls "frflow.project.effects.samples.Edges" then Some init_Edges_new_22 else
      if String.eqb cls "frflow.project.effects.samples.Numbers" then Some init_Numbers_new_31 else
      if String.eqb cls "frflow.project.effects.samples.Pair" then Some init_Pair_new_41 else
      if String.eqb cls "frflow.project.effects.samples.Scenarios" then Some init_Scenarios_new_44 else
      None)
    (fun s =>
      None)
    (fun s =>
      if sym_eqb s (Local "<by-name>" 2) then Some by_name_2 else
      if sym_eqb s (Local "<by-name>" 10) then Some by_name_10 else
      if sym_eqb s (Local "<by-name>" 37) then Some by_name_37 else
      if sym_eqb s (Local "<by-name>" 39) then Some by_name_39 else
      if sym_eqb s (Local "<by-name>" 38) then Some by_name_38 else
      if sym_eqb s (Local "<by-name>" 49) then Some by_name_49 else
      None).

End Units.

(** The definitions from outside the code calls, each with the arguments the staging took it to take
    unevaluated: the library says the same of each. *)
Definition Code_outside : list (sym * list bool) :=
  [((Member "scala.Int" ">=" "scala.Int:scala.Boolean"), []);
   ((Member "scala.Boolean" "&&" "scala.Boolean:scala.Boolean"), [true]);
   ((Member "scala.Int" ">" "scala.Int:scala.Boolean"), []);
   ((Member "scala.Int" "-" "scala.Int:scala.Int"), []);
   ((Member "scala.Int" "+" "scala.Int:scala.Int"), []);
   ((Member "scala.Int" "<" "scala.Int:scala.Boolean"), []);
   ((Member "scala.Int" "==" "scala.Int:scala.Boolean"), []);
   ((Member "scala.Int" "*" "scala.Int:scala.Int"), []);
   ((Member "scala.Int" "!=" "scala.Int:scala.Boolean"), []);
   ((Member "scala.Int" "<=" "scala.Int:scala.Boolean"), []);
   ((Member "scala.Boolean" "||" "scala.Boolean:scala.Boolean"), [true]);
   ((Member "scala.Boolean" "unary_!" ":scala.Boolean"), [])].

Lemma Code_outside_agrees : forallb (fun taken => Staged.takes (fst taken) (snd taken)) Code_outside = true.
Proof. vm_compute. reflexivity. Qed.

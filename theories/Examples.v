From Stdlib Require Import
  Arith            
  Classes.RelationClasses
  Morphisms
  Program.Basics
  List
  Lia.

From LEpic Require Import Syntax.


(* Playing around with ws and seq definitions... *)
Example ws_term_example : term :=
  (bag 2 3 
    (par (def 2 (lam (bag 0 2 (app 0 1))))
         (par (app 0 1)
              (def 1 (bng 1))))).

Theorem ws_term_example_is_ws :
  ws_term 2 3 ws_term_example.
Proof. apply ws_bag. simpl. apply ws_par.
  - apply ws_def. lia. 
    apply ws_lam. 
    apply ws_bag; simpl. 
    apply ws_app. lia. lia.
  - apply ws_par. 
    + apply ws_app. lia. lia.
    + apply ws_def. lia. 
      apply ws_bng. lia.
Qed.

Theorem ws_example_self_seq :
  seq_term ws_term_example ws_term_example.
Proof. apply seq_bag. apply seq_proc_refl. Qed.

Example seq_to_ws_example : term :=
  (bag 2 3 
    (par (par (def 1 (bng 1))
              (app 0 1))
        (def 2 (lam (bag 0 2 (app 0 1)))))).

Theorem is_seq_to_ws_example :
  seq_term seq_to_ws_example ws_term_example.
Proof. apply seq_bag. 
  assert (H0 : seq_proc
          (par (app 0 1) (def 1 (bng 1)))
          (par (def 1 (bng 1)) (app 0 1))).
  { apply seq_par_comm. }
  assert (H1 : seq_proc
          (par (def 2 (lam (bag 0 2 (app 0 1)))) (par (def 1 (bng 1)) (app 0 1)))
          (par (def 2 (lam (bag 0 2 (app 0 1)))) (par (app 0 1) (def 1 (bng 1))))).
  { apply seq_par_cong. 
    - apply seq_proc_refl.
    - apply seq_par_comm. }
  assert (H2 : seq_proc
          (par (par (def 1 (bng 1)) (app 0 1)) (def 2 (lam (bag 0 2 (app 0 1)))))
          (par (def 2 (lam (bag 0 2 (app 0 1)))) (par (def 1 (bng 1)) (app 0 1)))).
  { apply seq_par_comm. }
  apply seq_proc_trans with (P2 := par (def 2 (lam (bag 0 2 (app 0 1)))) (par (def 1 (bng 1)) (app 0 1))).
  - assumption.
  - assumption.
Qed. 
  

(* Identity Example *)
(* Note: Issues with list notation in tuples, so I use cons, etc. 
   e.g., 'tup [0;0]' corresponds to issues with term level. *)
   
Example id_ex : term := 
  bag 1 3 
    (par  (def 0 (lam (bag 0 1 (def 1 (tup (cons 0 (cons 0 nil)))))))
          (par (def 0 (bng 0)) 
               (par (app 0 1) (def 1 (tup (cons 2 (cons 2 nil))))))).

Theorem id_ex_is_ws : forall m n, 
    ws_term m n id_ex.
Proof. intros m n. apply ws_bag. apply ws_par.
    - apply ws_def. lia. 
      apply ws_lam; apply ws_bag; apply ws_def. lia.
      apply ws_tup; simpl. 
      apply Forall_cons. lia. apply Forall_cons. lia. apply Forall_nil.
    - apply ws_par. 
        + apply ws_def. lia. 
          apply ws_bng. lia.
        + apply ws_par.
            * apply ws_app. lia. lia.
            * apply ws_def. lia. 
              apply ws_tup. 
              apply Forall_cons. lia. apply Forall_cons. lia. apply Forall_nil.
Qed.
      
(* Importing at the top causes problems with using 'nil' in id_ex tuples. *)
From LEpic Require Import Contexts.

(*
Lemma otimes_to_add : forall m x y, ((delta m x y) ⊗ (zero m)) = ((delta (2*m) x y) ⨥ zero m ).
*)

Theorem id_ex_is_wf : forall m n, 
    wf_term m n (zero m) (zero n) id_ex.
Proof. intros m n.  
eapply wf_bag with  (G' := m[0 ↦ 1]) (D' :=  (SUM (n[0 ↦ 2] :: n[1 ↦ 2] :: n[2 ↦ 2] :: nil))). 
    - intros x H. assert (Hx: x = 0) by lia; subst. apply delta_id. 
    - intros x H. simpl. assert (Hx: x = 0 \/ x = 1 \/ x = 2) by lia. 
      destruct Hx as [Hx | [Hx | Hx]]. all : (subst; unfold sum; simpl; unfold zero; reflexivity).
    - (* apply wf_par. BUT need to rectify (m [0 ↦ 1] ⊗ zero m) and 
          (SUM (n [0 ↦ 2] :: n [1 ↦ 2] :: n [2 ↦ 2] :: nil) ⊗ zero n);
          e.g., (m [0 ↦ 1] ⊗ zero m) => 2*m [0 ↦ 1] ⨥ zero m ? *)
Admitted.
  
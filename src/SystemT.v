Require Import Maps.
Require Import Aux.
Require Import Coq.Logic.FunctionalExtensionality.

Require Import Coq.Bool.Bool.

(*****************************************************************************
 * DATATYPE DEFINITIONS AND OPERATIONS                                       *
 *****************************************************************************)

Inductive ty : Type :=
  | TNat : ty
  | TArrow : ty -> ty -> ty.

Inductive exp : Type :=
  | Var : id -> exp
  | Z : exp
  | S : exp -> exp
  | Rec : exp -> id -> id -> exp -> exp -> exp
  | Abs : id -> ty -> exp -> exp
  | App : exp -> exp -> exp.

Definition env : Type := partial_map ty.

Fixpoint subst (z : id) (e' : exp) (e : exp) : exp :=
  let do_subst := subst z e' in
  match e with
  | Var x as v => if beq_id x z then e' else v
  | Z => Z
  | S n => S (do_subst n)
  | Rec e0 x y e1 e =>
      let e1' := if beq_id x z || beq_id y z then e1 else do_subst e1 in
      Rec (do_subst e0) x y e1' (do_subst e)
  | Abs x t e as abs => if beq_id x z then abs else Abs x t (do_subst e)
  | App e1 e2 => App (do_subst e1) (do_subst e2)
  end.
Notation "'[' x ':=' e1 ']' e" := (subst x e1 e) (at level 70).

(*****************************************************************************
 * STATICS SPECIFICATION                                                     *
 *****************************************************************************)

Reserved Notation "Gamma |- e \in T" (at level 80).
Inductive has_type : env -> exp -> ty -> Prop :=
  | T_Var : forall Gamma x T,
              Gamma x = Some T -> Gamma |- Var x \in T
  | T_Z : forall Gamma, Gamma |- Z \in TNat
  | T_S : forall Gamma n, Gamma |- n \in TNat ->
                          Gamma |- S n \in TNat
  | T_Abs : forall Gamma t1 t2 x e,
              (update Gamma x t1) |- e \in t2 ->
              Gamma |- Abs x t1 e \in (TArrow t1 t2)
  | T_App : forall Gamma e1 e2 t t2,
              Gamma |- e1 \in TArrow t2 t -> Gamma |- e2 \in t2 ->
              Gamma |- App e1 e2 \in t
  | T_Rec : forall Gamma e0 x y e1 e t,
              Gamma |- e \in TNat -> Gamma |- e0 \in t ->
              x <> y ->
              (update (update Gamma y t) x TNat) |- e1 \in t ->
              Gamma |- (Rec e0 x y e1 e) \in t
where "Gamma |- e \in T" := (has_type Gamma e T).

Inductive value : exp -> Prop :=
  | Val_Z : value Z
  | Val_S : forall n, value n -> value (S n)
  | Val_Abs : forall x t e, value (Abs x t e).

Inductive nat_value : exp -> Prop :=
  | NatVal_Z : nat_value Z
  | NatVal_S : forall n, nat_value n -> nat_value (S n).

Inductive appears_free_in : id -> exp -> Prop :=
  | Afi_Var : forall x, appears_free_in x (Var x)
  | Afi_S : forall x e, appears_free_in x e -> appears_free_in x (S e)
  | Afi_App1 : forall x e1 e2,
      appears_free_in x e1 -> appears_free_in x (App e1 e2)
  | Afi_App2 : forall x e1 e2,
      appears_free_in x e2 -> appears_free_in x (App e1 e2)
  | Afi_Abs : forall x y t e,
      x <> y -> appears_free_in x e ->
      appears_free_in x (Abs y t e)
  | Afi_Rec : forall x y z e0 e1 e,
      appears_free_in z e -> appears_free_in z (Rec e0 x y e1 e)
  | Afi_RecZ : forall z e0 x y e1 e,
      appears_free_in z e0 -> appears_free_in z (Rec e0 x y e1 e)
  | Afi_RecS : forall z e0 x y e1 e,
      x <> z -> y <> z -> appears_free_in z e1 ->
      appears_free_in z (Rec e0 x y e1 e).

Definition closed (e : exp) :=
  forall x, ~ appears_free_in x e.


(*****************************************************************************
 * DYNAMICS SPECIFICATION                                                    *
 *****************************************************************************)

Reserved Notation "e ==> e'" (at level 75).
Inductive step : exp -> exp -> Prop :=
  | S_Succ : forall e e', e ==> e' -> S(e) ==> S(e')
  | S_App1 : forall e1 e1' e2,
      e1 ==> e1' -> App e1 e2 ==> App e1' e2
  | S_App2 : forall e1 e2 e2',
      value e1 -> e2 ==> e2' -> App e1 e2 ==> App e1 e2'
  | S_AppAbs : forall e e2 x t,
      value e2 -> App (Abs x t e) e2 ==> [x := e2] e
  | S_Rec1 : forall e0 x y e1 e e',
      e ==> e' -> Rec e0 x y e1 e ==> Rec e0 x y e1 e'
  | S_RecZ : forall e0 x y e1, Rec e0 x y e1 Z ==> e0
  | S_RecS : forall e0 x y e1 e,
      value (S e) -> Rec e0 x y e1 (S e) ==>
                    [x := e][y := (Rec e0 x y e1 e)] e1
where "e ==> e'" := (step e e').

Reserved Notation "e ==>* e'" (at level 75).
Inductive multistep : exp -> exp -> Prop :=
  | Multi_Refl : forall e, e ==>* e
  | Multi_Step : forall e e' e'', e ==> e' -> e' ==>* e'' -> e ==>* e''
where "e ==>* e'" := (multistep e e').

(*****************************************************************************)
Hint Constructors ty exp has_type value nat_value appears_free_in step multistep.
(*****************************************************************************)

(*****************************************************************************
 * STATIC LEMMAS                                                             *
 *****************************************************************************)

Lemma free_in_context : forall x e t Gamma,
   appears_free_in x e ->
   Gamma |- e \in t ->
   exists t', Gamma x = Some t'.
Proof with auto.
  intros x e t Gamma Hfree Hte.
  generalize dependent t. generalize dependent Gamma.
  induction Hfree; try (intros Gamma t Ht;
    inversion Ht; subst; clear Ht; solve [eauto]).

  - intros Gamma t2 Ht. inversion Ht; subst; clear Ht.
    apply IHHfree in H5. rewrite update_neq in H5.
     + assumption.
     + rewrite symmetry_neq. assumption.

  - intros Gamma t2 Ht. inversion Ht; subst; clear Ht.
    apply IHHfree in H11.
    rewrite update_neq in H11...
    rewrite update_neq in H11...
Qed.

Lemma typable_empty_closed : forall e t,
    empty |- e \in t  -> closed e.
Proof.
  intros e t Hempty x Hfree.
  apply free_in_context with (t:=t) (Gamma:=empty) in Hfree.
  - inversion Hfree. inversion H.
  - assumption.
Qed.

Lemma weakening : forall Gamma Gamma' e t,
     Gamma |- e \in t  ->
     (forall x, appears_free_in x e -> Gamma x = Gamma' x) ->
     Gamma' |- e \in t.
Proof with eauto.
  intros.
  generalize dependent Gamma'.
  induction H; intros Gamma' Hfree; auto.
  - apply T_Var. rewrite <- Hfree...
  - apply T_Abs. apply IHhas_type. intros x1 Hx1_free.
    unfold update. unfold t_update. destruct (beq_id x x1) eqn: Heq.
    + reflexivity.
    + rewrite beq_id_false_iff in Heq.
      rewrite Hfree...
  - apply T_App with t2...
  - apply T_Rec... apply IHhas_type3. intros x1 Hx1_free.
    unfold update. unfold t_update.
    destruct (beq_id x x1) eqn: Heqx...
    destruct (beq_id y x1) eqn: Heqy...
    rewrite beq_id_false_iff in Heqx.
    rewrite beq_id_false_iff in Heqy.
    apply Hfree. apply Afi_RecS...
Qed.

Lemma closed_typable_empty :
  forall Gamma e t, Gamma |- e \in t -> closed e ->
                    empty |- e \in t.
Proof with eauto.
  intros Gamma e t Hte Hclosed.
  unfold closed in Hclosed. unfold not in Hclosed.
  generalize dependent Gamma. generalize dependent t.
  induction e; try intros t Gamma Ht.
  - exfalso. eapply Hclosed...
  - eapply weakening. eassumption.
    intros x Hafi. apply Hclosed in Hafi. inversion Hafi.
  - eapply weakening. eassumption.
    intros x Hafi. apply Hclosed in Hafi. inversion Hafi.
  - rename e1 into e0. rename i into x. rename i0 into y.
    rename e2 into e1. rename e3 into e.
    inversion Ht; subst; clear Ht. apply T_Rec...
Admitted.

Lemma substitution_preserves_typing : forall Gamma e e' t t' x,
  update Gamma x t |- e' \in t' -> empty |- e \in t ->
  Gamma |- [x := e] e' \in t'.
Proof with eauto.
  intros Gamma e e' t t' x Hte' Hte.
  generalize dependent Gamma.
  generalize dependent t'.
  induction e'; subst; intros t' Gamma H;
  inversion H; simpl; subst...
  - rename i into y. destruct (beq_idP y x) as [Hyx|Hyx].
    + subst.
      rewrite update_eq in H2. inversion H2; subst.
      apply weakening with empty. assumption.

      intros y Hy_free.
      apply typable_empty_closed in Hte. unfold closed in Hte.
      apply Hte in Hy_free. inversion Hy_free.
    + apply T_Var. rewrite update_neq in H2.
      * assumption.
      * rewrite symmetry_neq. assumption.
  - rename x into z. rename i into x. rename i0 into y.
    apply T_Rec...
    destruct (beq_idP x z) as [Hxz|Hxz]...
    + subst. simpl. rewrite update_split_shadow in H10...
    + destruct (beq_idP y z) as [Hyz|Hyz]...
      * subst. simpl. rewrite update_shadow in H10...
      * simpl. apply IHe'2.
        rewrite update_permute...
        assert (Hhelp: update (update Gamma y t') z t =
                       update (update Gamma z t) y t').
        { rewrite update_permute... }
        rewrite Hhelp...
  - rename i into y. destruct (beq_idP y x) as [Hyx|Hyx].
    + subst. apply T_Abs. rewrite update_shadow in H5...
    + apply T_Abs. apply IHe'. rewrite update_permute...
Qed.

(*****************************************************************************
 * DYNAMIC LEMMAS                                                            *
 *****************************************************************************)

(*****************************************************************************
 * EXERCISE SOLUTIONS                                                        *
 *****************************************************************************)

(* Exercise 9.1 - Prove Lemma 9.2 *)
Lemma canonical_nat : forall Gamma e,
  value e -> Gamma |- e \in TNat ->
  e = Z \/ exists e', e = (S e').
Proof.
  intros Gamma e Hv HNat.
  inversion Hv; subst; clear Hv.
  - left. reflexivity.
  - right. exists n. reflexivity.
  - inversion HNat.
Qed.

Lemma canonical_arrow : forall Gamma t1 t2 e,
  value e -> Gamma |- e \in TArrow t1 t2 ->
  exists x e2, e = Abs x t1 e2.
Proof.
  intros Gamma t1 t2 e Hv Harrow.
  remember (TArrow t1 t2).
  inversion Hv; subst; clear Hv.
  - inversion Harrow.
  - inversion Harrow.
  - exists x. exists e0.
    inversion Harrow; subst; clear Harrow.
    reflexivity.
Qed.

Lemma canonical_forms :
  forall Gamma e, value e ->
              (Gamma |- e \in TNat -> (e = Z \/ exists e', e = S e')) \/
              (forall t1 t2, Gamma |- e \in TArrow t1 t2 ->
                             exists x e2, e = Abs x t1 e2).
Proof with eauto.
  intros Gamma e Hve.

  inversion Hve; subst; clear Hve.
  - left. apply canonical_nat...
  - left. apply canonical_nat...
  - right. intros t1 t2. eapply canonical_arrow...
Qed.

(*****************************************************************************)
(* Exercise 9.2 - Prove Lemma 9.3 *)

Lemma preservation : forall e e' t,
  empty |- e \in t -> e ==> e' -> empty |- e' \in t.
Proof with eauto.
  intros e e' t Ht Hstep.
  generalize dependent e'.
  remember empty.
  induction Ht;
  try solve [subst; intros e' Habsurd; inversion Habsurd; subst; eauto].

  - intros e_appd Hstep. inversion Hstep; subst; clear Hstep...
    inversion Ht1; subst; clear Ht1.
    eapply substitution_preserves_typing...

  - intros e_appd Hstep. inversion Hstep; subst; clear Hstep...
    apply substitution_preserves_typing with (t:=TNat)...
    + specialize (IHHt1 (eq_refl empty)).
      specialize (IHHt2 (eq_refl empty)).

      apply substitution_preserves_typing with (t:=t)...
      * rewrite update_permute...
      * apply T_Rec...
        inversion Ht1...
    + inversion Ht1...
Qed.

(*****************************************************************************)
(* Exercise 9.3 - Prove Normalization to Nat *)

Lemma multi_succ : forall e n, e ==>* n -> S e ==>* S n.
Proof.
  intros e n Hstep. induction Hstep.
  - apply Multi_Refl.
  - eapply Multi_Step with (e':=S e').
    + apply S_Succ. assumption.
    + assumption.
Qed.

Lemma multi_app : forall e1 e2 e1' e2',
  e1 ==>* e1' -> e2 ==>* e2' -> value e1' -> App e1 e2 ==>* App e1' e2'.
Proof with eauto.
  intros e1 e2 e1' e2' Hstep1 Hstep2 Hval.
  induction Hstep1.
  - induction Hstep2.
    + apply Multi_Refl.
    + eapply Multi_Step...
  - eapply Multi_Step...
Qed.

Lemma normalizing_nat :
  forall e, empty |- e \in TNat -> exists n, nat_value n /\ e ==>* n.
Proof with eauto.
  intros e Hte. remember empty. remember TNat.
  induction Hte; subst...
  - inversion H.
  - destruct IHHte... destruct H. clear Heqt.
    exists (S x). split... apply multi_succ. assumption.
  - inversion Heqt.
  - give_up.
Abort.
(* The proof breaks down due to the inability of the inductive hypothesis
   to handle function application. Despite clearing the base cases with a
   maximally general inductive hypothesis, the inductive hypothesis only
   encompasses values that type to Nat, but application may be on functions
   from ANYTHING to Nat. *)

(*****************************************************************************)
(* Exercise 9.4 - Prove Normalization of Well-Typed Terms *)

Lemma multi_preservation :
  forall e e' t, empty |- e \in t -> e ==>* e' -> empty |- e' \in t.
Proof with eauto.
  intros e e' t Hte Hstep. induction Hstep...
  apply IHHstep. eapply preservation...
Qed.

Lemma multi_trans : forall e e' e'',
  e ==>* e' -> e' ==>* e'' -> e ==>* e''.
Proof with eauto.
  intros e e' e'' Hstep1 Hstep2.
  induction Hstep1...
Qed.

Lemma closed_succ : forall e, closed (S e) -> closed e.
Proof with eauto.
  intros e Hcse. unfold closed in Hcse. unfold not in Hcse.
  induction e; intros x Hfree...
Qed.

Lemma closed_app : forall e1 e2, closed (App e1 e2) -> closed e1 /\ closed e2.
Proof with eauto.
  intros e1 e2 Hcse. unfold closed in Hcse. unfold not in Hcse.
  split.
  - induction e1; intros x Hfree...
  - induction e2; intros x Hfree...
Qed.

Theorem termination : forall Gamma e t,
  Gamma |- e \in t -> closed e -> exists e', value e' /\ e ==>* e'.
Proof with eauto.
  intros Gamma e t Hte Hclosed.
  induction Hte; subst.
  - exfalso. unfold closed in Hclosed. unfold not in Hclosed. eapply Hclosed...
  - exists Z...
  - destruct IHHte...
    + apply closed_succ...
    + exists (S x). destruct H. split.
      * apply Val_S...
      * apply multi_succ...
  - eexists...
  - apply closed_app in Hclosed. destruct Hclosed as [Hcl_e1 Hcl_e2].
    destruct IHHte1; destruct IHHte2...
    destruct H. destruct H0.
    rename t2 into t1. rename t into t2. rename x into v2. rename x0 into v1.

    apply closed_typable_empty in Hte1...
    apply closed_typable_empty in Hte2...

    assert (Htv2:=Hte1).
    eapply multi_preservation in Htv2...
    apply canonical_arrow in Htv2...
    destruct Htv2 as (x & e_body & Heq). subst.

    rename v1 into v2. eexists. split.

    + admit.
    + apply multi_trans with (e':=App (Abs x t1 e_body) v2).
      * apply multi_app...
      * eapply Multi_Step.
        -- apply S_AppAbs...
        -- give_up. (* PROBLEM *)
  - admit.
  Unshelve. assumption.
Abort.

(* The problem arises after substitution occurs in the application case.
   There is nothing in the hypotheses that speaks to the ability of the
   body to reduce to a value (as needed to satisfy the prior admitted case. *)

(*****************************************************************************)
(* Hereditary Termination *)
(*

Definition terminating_nat e :=
  exists e', e ==>* e' /\ nat_value e'.

Inductive hereditarily_terminating : exp -> ty -> Prop :=
  | HT_Nat : forall e, terminating_nat e ->
             hereditarily_terminating e TNat
  | HT_Arrow : forall e t1 t2,
                   (forall e1, hereditarily_terminating e1 t1 ->
                   hereditarily_terminating (App e e1) t2) ->
                   hereditarily_terminating e (TArrow t1 t2).

Lemma hereditary_termination :
  forall e t, empty |- e \in t -> hereditarily_terminating e t.
Proof with eauto.
  intros e t. generalize dependent e. induction t.
  - intros e Ht. apply HT_Nat... unfold terminating_nat. intros _.

*)

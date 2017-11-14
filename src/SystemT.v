Load Maps.

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
              (update (update Gamma y t) x TNat) |- e1 \in t ->
              Gamma |- (Rec e0 x y e1 e) \in t
where "Gamma |- e \in T" := (has_type Gamma e T).

Inductive value : exp -> Prop :=
  | Val_Z : value Z
  | Val_S : forall n, value n -> value (S n)
  | Val_Abs : forall t x e, value (Abs x t e).

Lemma canonical_nat : forall Gamma e,
  value e -> Gamma |- e \in TNat ->
  e = Z \/ exists e', e = (S e').
Proof.
  intros Gamma e Hv HNat.
  remember TNat. inversion Hv; subst; clear Hv.
  - left. reflexivity.
  - right. exists n. reflexivity.
  - inversion HNat.
Qed.





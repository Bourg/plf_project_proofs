Require Import Maps.
Require Import Coq.Logic.FunctionalExtensionality.

Lemma symmetry_neq : forall {T : Type} (P Q : T), P <> Q <-> Q <> P.
Proof.
  intros P Q. split; intros Hneq Heq; subst; apply Hneq; reflexivity.
Qed.

Lemma update_split_shadow: forall T (Gamma : partial_map T) x y a b c,
        update (update (update Gamma x a) y b) x c =
        update (update Gamma y b) x c.
Proof with auto.
  intros T Gamma x y a b c.
  apply functional_extensionality. intros z.
  unfold update. unfold t_update.
  destruct (beq_idP x z); subst...
Qed.
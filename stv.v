Require Import Coq.Lists.List.
Require Import Coq.Init.Datatypes.
Import ListNotations.
Section STV.
Require Export Arith.

Definition nty  : nat -> nat := fun x => 0.          (* null tally *)

Inductive PD  {A: Type} : list A -> Prop :=
   PDe :  PD  ( nil)
 | PDc :  forall a:A,forall l: list A, PD l /\ ~(In a l) -> (PD  (cons a l)).

Definition cand := nat.
Definition ballot := (nat * (list cand)) % type.

Definition s_first_pref_column := (nat   (* candidate index *)
                                 * nat   (* preference      *)
                                 * nat   (* weight          *)
                                ) % type.
Definition s_first_preference_ballot := list s_first_pref_column.

Inductive SNode :=
    sstate:                             (** intermediate states             **)
       (list s_first_preference_ballot) (*  first-preference representation  *)
     * (list cand)                      (*  hopefuls                         *)
     * (nat -> nat)                     (*  tallies                          *)
     -> SNode
  | swinners:                           (** final state                     **)
       (list cand)
     -> SNode.                          (*  election winners                 *)


Definition spf_ft_fpc_cand (col : s_first_pref_column) : nat :=
  match col with
  | (c, _, _) => c
  end.
Definition spf_ft_fpc_weight (col : s_first_pref_column) : nat :=
  match col with
  | (_, _, w) => w
  end.

Definition spf_ft_add_weights_b (c : nat) (b : s_first_preference_ballot)  : nat :=
  fold_left plus
            (map spf_ft_fpc_weight (filter
                             (fun x : s_first_pref_column => beq_nat (spf_ft_fpc_cand x) c)
                             b))
            0.

Definition spf_ft_add_weights (b : list s_first_preference_ballot) (c : nat) : nat :=
  fold_left plus
            (map (spf_ft_add_weights_b c) b)
            0.

Inductive SPf (b: list ballot) (q: nat) (s: nat) : SNode -> Type :=
  spf_ax : forall f h t,
  PD h ->
  t = nty ->
  SPf b q s (sstate (f, h, t))
| spf_ft : forall f h t  tn, (** compute first preference tallies **)
  SPf b q s (sstate (f, h, t)) ->
    (forall i : nat, (In i h) -> tn i = spf_ft_add_weights f i) ->
  SPf b q s (sstate (f, h, tn)).


Variable encrypt : nat -> nat.
Variable decrypt : nat -> nat.
Hypothesis decrypt_inverse : forall (n : nat), decrypt(encrypt n) = n.
Lemma encrypt_inverse : forall (n m : nat), encrypt n = m -> decrypt m = n.
Proof.  intros n m c. rewrite <- c. apply decrypt_inverse.
Qed.

Variable h_add : nat -> nat -> nat.
Hypothesis h_add_homomorphism : forall (n m : nat), h_add (encrypt n) (encrypt m) = encrypt (n + m).

Lemma h_add_commutative : forall (n m : nat), h_add (encrypt n) (encrypt m) = h_add (encrypt m) (encrypt n).
Proof.  intros n m. rewrite -> h_add_homomorphism. rewrite -> h_add_homomorphism. rewrite -> plus_comm. reflexivity.
Qed.

Lemma h_add_fold_left_homomorphism : forall (l : list nat),
  fold_right h_add (encrypt 0) (map encrypt l)
   = encrypt (fold_right plus 0 l).
Proof.  intros l. induction l.
          simpl. reflexivity.
          rewrite -> map_cons. simpl. rewrite -> IHl. rewrite -> h_add_homomorphism. reflexivity.
Qed.

Lemma h_add_fold_left_inverse_homomorphism : forall (l : list nat),
  decrypt (fold_right h_add (encrypt 0) (map encrypt l))
   = fold_right plus 0 l.
Proof.  intros l. rewrite -> h_add_fold_left_homomorphism. apply decrypt_inverse.
Qed.

Definition ss_first_pref_column := (nat   (* candidate index, plaintext *)
                                 * nat (* preference, encrypted      *)
                                 * nat (* weight, encrypted          *)
                                ) % type.
Definition ss_first_preference_ballot := list ss_first_pref_column.

Inductive SSNode :=
    ssstate:                            (** intermediate states             **)
       (list ss_first_preference_ballot)  (*  first-preference representation  *)
     * (list nat)                      (*  hopefuls                         *)
     * (nat -> nat)                    (*  tallies                          *)
     -> SSNode
  | sswinners:                          (** final state                     **)
       (list cand)
     -> SSNode.                         (*  election winners                 *)

Definition encrypt_p_w (b : s_first_pref_column) : ss_first_pref_column :=
  match b with
  | (x, y, z) => (x, encrypt y, encrypt z)
  end.

Definition encrypt_s_first_preference_ballot : s_first_preference_ballot -> ss_first_preference_ballot :=
  map encrypt_p_w.

Definition encrypt_snode_first_pref : list s_first_preference_ballot -> list ss_first_preference_ballot :=
  map encrypt_s_first_preference_ballot.

Definition encrypt_snode (n : SNode) : SSNode :=
  match n with
  | sstate (a, b, c) => ssstate (encrypt_snode_first_pref a, b, c)
  | swinners (a) => sswinners (a)
  end.

Definition sspf_ft_fpc_cand (col : ss_first_pref_column) : nat :=
  match col with
  | (c, _, _) => c
  end.
Definition sspf_ft_fpc_weight (col : ss_first_pref_column) : nat :=
  match col with
  | (_, _, w) => w
  end.

Definition sspf_ft_add_weights_b_f (c : nat) (x : ss_first_pref_column) : bool :=
  beq_nat (sspf_ft_fpc_cand x) c.

Definition sspf_ft_add_weights_b (c : nat) (b : ss_first_preference_ballot)  : nat :=
  fold_left h_add
            (map sspf_ft_fpc_weight (filter
                             (sspf_ft_add_weights_b_f c)
                             b))
            (encrypt 0).

Lemma spf_ft_add_weights_b_homomorphism : forall (c : nat) (b : s_first_preference_ballot),
  encrypt (spf_ft_add_weights_b c b) = sspf_ft_add_weights_b c (encrypt_s_first_preference_ballot b).
Proof.  intros c b. induction b.
          simpl. unfold spf_ft_add_weights_b. unfold sspf_ft_add_weights_b. simpl. reflexivity.
          unfold encrypt_s_first_preference_ballot. rewrite -> map_cons.


Definition sspf_ft_add_weights (b : list ss_first_preference_ballot) (c : nat) : nat :=
  fold_left h_add
            (map (sspf_ft_add_weights_b c) b)
            (encrypt 0).


Inductive SSPf (b: list ballot) (q: nat) (s: nat) : SSNode -> Type :=
  sspf_ax : forall f h t,
  PD h ->
  t = nty ->
  SSPf b q s (ssstate (f, h, t))
| sspf_ft : forall f h t  tn, (** compute first preference tallies **)
  SSPf b q s (ssstate (f, h, t)) ->
    (forall i : nat, (In i h) -> tn i = decrypt (sspf_ft_add_weights f i)) ->
  SSPf b q s (ssstate (f, h, tn)).



Theorem pf_ft_s_ss : forall b q s n,
  SPf b q s n ->
  SSPf b q s (encrypt_snode n).
Proof.  intros b q s n p. induction p.
          apply sspf_ax. apply p. apply e.
          apply sspf_ft with (t := t).
            unfold encrypt_snode in IHp. apply IHp.
            intros i j. specialize (e i). specialize (e j).
                
            

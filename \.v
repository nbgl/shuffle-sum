(* simple stv *)

Require Import Notations.
Require Import Coq.Lists.List.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.omega.Omega.
Require Import Coq.Arith.Le.
Require Import Coq.Arith.Compare_dec.
Import ListNotations.

(* notation for type level existential quantifier *)
Notation "'existsT' x .. y , p" := (sigT (fun x => .. (sigT (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'existsT' '/ ' x .. y , '/ ' p ']'")
  : type_scope.

(* STV counting for finite types with decidable equality *)
Section STV.

(* lists with pairwise distinct candidates *)
Inductive PD  {A: Type} : list A -> Prop :=
   PDe :  PD  ( nil)
 | PDc :  forall a:A,forall l: list A, PD l /\ ~(In a l) -> (PD  (cons a l)).

Variable cand: Type.
Variable cand_all: list cand.
Hypothesis cand_pd: PD cand_all.
Hypothesis cand_finite: forall c, In c cand_all.
Hypothesis cand_eq_dec: forall c d:cand, {c=d} + {c<>d}.

(* a ballot is a list of candidates *)
Definition ballot := list cand.

(* intermediate and final states in vote counting *)
Inductive Node :=
   state:                     (** intermediate states **)
       list ballot            (* uncounted votes *)
     * (cand -> list ballot)  (* assignment of counted votes to first pref candidate *)
     * (cand -> nat)          (* tally *)
     * (list cand)            (* hopeful cands still in the running *)
     * (list cand)            (* defeated cands no longer in the running *)
     -> Node
  | winners:                  (** final state **)
    list cand -> Node.        (* election winners *)

(* shorthands *)
Definition nbdy : list cand := [].                    (* empty candidate list *)
Definition nty  : cand -> nat := fun x => 0.          (* null tally *)
Definition nas  : cand -> list ballot := fun x => []. (* null vote assignment *)

(* the new tally is the old tally with c's votes incremented by one *)
Definition inc (c:cand) (t: cand -> nat) (nt: cand -> nat) : Prop :=
  (nt c = t c + 1)%nat /\  forall d, d <> c -> nt d = t d.

(* the new assignment is the old assignment with ballot b added for candidate c *)
Definition add (c:cand) (b:ballot) (a: cand -> list ballot) (na: cand -> list ballot) : Prop :=
  na c = b::(a c) /\  forall d, d <> c -> na d = a d.

(* l and nl are equal except that nl additionally contaeqe x *)
Definition eqe {A: Type} (x:A) (l: list A) (nl: list A) : Prop :=
  exists l1 l2: list A, l = l1 ++ l2 /\ nl = l1 ++ [x] ++ l2.

(* l contaeqe x and replacing x with y in l yields nl *)
Definition rep {A:Type} (x y: A) (l nl: list A) :=
  exists l1 l2: list A, l = l1 ++ [x] ++ l2 /\ nl = l1 ++ [y] ++ l2.

Inductive Pf (b: list ballot) (q: nat) (s: nat) : Node -> Type := 
  ax :  forall  u a t h e,                      (* start counting *)
  (forall c: cand, In c h) ->                   (* if all candidates are hopeful and *)
  PD h ->                                       (* hopefuls are pairwise distinct *)
  u = b ->                                      (* if the list of ballots contaeqe all ballots *)
  a = nas ->                                    (* and the initial assignment is the null assignment *)
  t = nty ->                                    (* and we begin with the null tally *)
  e = nbdy ->                                   (* and nobody is elected initially *)
  Pf b q s (state (u, a, t, h, e))              (* we start counting with null tally, assignment and elected cands *)
| c1 : forall u nu a na t nt h e f fs,          (** count one vote **)
  Pf b q s (state (u, a, t, h, e )) ->          (* if we are counting votes *)
  eqe (f::fs) nu u ->                           (* and del'ing a vote with 1st pref f yields new list of uncounteds *)
  In f h ->                                     (* and f is a hopeful *)
  t f < q ->                                    (* and this isn't surplus *)
  add f (f::fs) a na ->                         (* and the new assignment records the vote for f *)
  inc f t nt ->                                 (* and the new tally increments the votes for f by one *)
  Pf b q s (state (nu, na, nt, h, e))           (* we continue with updated tally and assignment *)
| el : forall u a t h nh e ne c,                (** elect a candidate **)
  Pf b q s (state (u, a, t, h, e)) ->           (* if we have an uncounted vote with 1st preference f *)
  In c h ->                                     (* and c is a hopeful *)
  t(c) = q ->                                   (* and c has enough votes *)
  length e < s ->                               (* and there are still unfilled seats *)
  eqe c nh h ->                                 (* and f has been removed from the new list of hopefuls *)
  eqe c e ne ->                                 (* and del'ing c from the new elected cands gives old elected *)
  Pf b q s (state (u, a, t, nh, ne))            (* then proceed with updated  hopefuls and elected cands *)
| tv : forall u nu a t h e f fs,                (** transfer vote **)
  Pf b q s (state (u, a, t, h, e)) ->           (* if we are counting votes *)
  ~(In f h) ->                                  (* and f no longer in the running *)
  rep (f::fs) fs u nu ->                        (* and the uncounted votes are updated by deleting first pref f from a vote *)
  Pf b q s (state (nu, a, t, h, e))             (* we continue with updated set of uncounted votes *)
| ey : forall u nu  a t h e,                    (** empty vote **)
  Pf b q s (state (u, a, t, h, e)) ->           (* if we are counting votes *)
  eqe [] nu u ->                                (* and an empty vote is removed from uncounted votes *)
  Pf b q s (state (nu, a, t, h, e))             (* continue with updated set of uncounted votes *)
| tl : forall u a t h nh e c,                   (** transfer least **)
  Pf b q s (state ([], a, t, h, e)) ->          (* if we have no uncounted votes *)
  length e + length h > s ->                    (* and there are still too many candidates *)
  In c h  ->                                    (* and candidate c is still hopeful *)
  (forall d, In d h-> t c <= t d) ->            (* but all others have more votes *)
  eqe c nh h ->                                 (* and c has been removed from the new list of hopefuls *)
  u = a(c) ->                                   (* and marked to be transfered *)
  Pf b q s (state (u, a, t,nh, e))              (* transfer c's votes and proceed with new hopefuls *)
| hw : forall w u a t h e,                      (** hopefuls win **)
  Pf b q s (state (u, a, t, h, e)) ->           (* if at any time *)
  length e + length h <= s ->                   (* we have more hopefuls and electeds  than seats *)
  w = e ++ h ->                                 (* and the winning candidates are their union *)
  Pf b q s (winners (w))                        (* the elected cands and the remaining hopefuls are declared winners *)
| ew : forall w u a t h e,                      (** elected win **)
  Pf b q s (state (u, a, t, h, e)) ->           (* if at any time *)
  length e = s ->                               (* we have as many elected candidates as setas *) 
  w = e ->                                      (* and the winners are precisely the electeds *)
  Pf b q s (winners w).                         (* they are declared the winners *)

(* definitions for auxilary constructors *)
(* prefixing is one way of conjoining *)
Lemma ins_hd {A: Type}: forall c: A, forall l: list A, eqe c l (c::l).
  Proof.
  intros c l.
  unfold eqe.
  exists ([]: list A). exists l. split.
  auto. auto.
Qed.

(* increment tally for cand by one *)
Definition inct (c:cand) (t: cand -> nat) : cand -> nat :=
  fun d => if (cand_eq_dec c d) then (S(t d))%nat else (t d).

Lemma inct_ok: forall c:cand, forall t: cand -> nat, inc c t (inct c t).
Proof.
  intros. unfold inc. split.
  Functional Scheme inct_ind := Induction for inct Sort Prop.
  functional induction  (inct c t c). omega.
  assert False. apply (_x). trivial. elim H.
  intros d ass.
  functional induction (inct c t d).
  assert False. apply ass. trivial. elim H. trivial.
Qed. 

(* add ballot to vote assignment  for cand *)
Definition adda (c:cand) (b:ballot) (a: cand -> list ballot) : cand -> list ballot :=
  fun d => if (cand_eq_dec c d) then (b::(a d)) else (a d).

Lemma adda_ok : forall c: cand, forall b: ballot, forall a: cand -> list ballot, add c b a (adda c b a).
Proof.
  intros. unfold adda. unfold add. destruct (cand_eq_dec c c). split. trivial.
  intros d ass. destruct (cand_eq_dec c d).  contradict ass. auto. trivial.
  split. contradict n. trivial. contradict n. trivial.
Qed.

(* remove one occurrence of a candidate from a list *)
Fixpoint remc (c: cand) (l: list cand) :=
  match l with 
    nil => nil
  | cons l0 ls => if (cand_eq_dec c l0) then ls else cons l0 (remc c ls)
  end.

Lemma remc_ok : forall c:cand, forall l:list cand, In c l -> eqe c (remc c l) l.
Proof.
  intros c l. induction l as [| l0 ls IHls].
  intro i. contradict i.
  intro i.
  assert (H: {l0=c} + {l0<>c}) by apply (cand_eq_dec l0 c).
  destruct H as [l0eqc | l0neqc ].
  replace (remc c (l0::ls)) with ls.
  unfold eqe. 
  exists ([]: list cand). exists ls. split.
  auto. replace c with l0. auto.
  replace c with l0. unfold remc. destruct (cand_eq_dec l0 l0). trivial.
  contradict n. trivial.
  (* we must have that In c ls *)
  assert (Hin: l0 = c \/ In c ls) by apply (in_inv i).
  destruct Hin as [l0eqc | Hin ]. 
  contradict l0neqc. assumption.
  (* apply IH *)
  assert (eqe c (remc c ls) ls) by apply (IHls Hin).
  unfold eqe in H.
  replace (remc c (l0::ls)) with (l0::(remc c ls)).
  destruct H as [l1 H]. destruct H as [l2 H]. destruct H as [lft rgt].
  unfold eqe.
  exists (l0::l1). exists l2.
  split.
  transitivity (l0::(l1++l2)). congruence. auto.
  transitivity (l0::(l1 ++ [c] ++ l2)). congruence. auto.
  unfold remc.
  destruct (cand_eq_dec c l0). contradict l0neqc. symmetry. assumption. trivial.
Qed.

(* auxilary constructors *)
(** ax **)
Definition ax_aux : forall b q s,
  Pf b q s (state (b, nas, nty, cand_all, ([]: list cand))).
Proof.
  intros  b q s.
  apply (ax b q s b nas nty cand_all ([]: list cand)).
  trivial. trivial. trivial. trivial. trivial. unfold nbdy. trivial.
Defined.

(** count one *)
Definition c1_aux : forall b q s f fs u a  t  h e,
  Pf b q s (state ((f::fs)::u, a, t, h, e)) ->
  In f h ->
  t f < q ->
  Pf b q s (state (u, adda f (f::fs) a, inct f t, h, e)).
Proof.
  intros b q s f fs u a t h e p hin hlt.
  apply (c1 b q s ((f::fs)::u) u a (adda f (f::fs) a) t (inct f t) h e f fs).
  assumption. apply (ins_hd (f::fs) u). assumption. assumption.  apply (adda_ok f (f::fs) a). apply (inct_ok f t).
Defined.

(** elect **)
Definition el_aux : forall b q s u a t h e c,
  Pf b q s (state (u, a, t, h, e)) ->
  In c h ->
  length e < s ->
  t c = q ->
  Pf b q s (state (u, a, t, remc c h, c::e)).
Proof.
  intros b q s u a t h e c p hin hlen heq.
  apply (el b q s u a  t h (remc c h) e (c::e) c).
  assumption. assumption. assumption. assumption.
  apply (remc_ok c h). assumption. trivial. apply (ins_hd c e).
Defined.

(** empty vote **)
Definition ey_aux: forall b q s u a t h e,
  Pf b q s (state (([]::u), a, t, h, e)) ->
  Pf b q s (state (u, a, t, h, e)).
Proof.
  intros b q s u a t h e p.
  apply (ey b q s ([]::u) u a t h e p).
  apply (ins_hd [] u).
Defined.

(* transfer vote *)
Definition tv_aux : forall b q s f fs u a t h e,
  Pf b q s (state ((f::fs)::u, a, t, h, e)) ->
  ~(In f h) ->
  Pf b q s (state (fs::u, a, t, h, e)).
Proof.
  intros b q s f fs u a t h e p ass.
  apply (tv b q s ((f::fs)::u) (fs::u) a t h e f fs).
  assumption. assumption. unfold rep. exists ([]: list (list cand)).
  exists u. split. auto. auto.
Defined.

Definition tl_aux : forall b q s a t h e c,
  Pf b q s (state([], a, t, h, e)) ->
  length e + length h > s ->
  In c h ->
  (forall d, In d h-> t c <= t d) ->
  Pf b q s (state (a(c), a, t, (remc c h), e)).
Proof.
  intros.
  apply (tl b q s (a c) a t h (remc c h) e c).
  assumption. assumption. assumption. assumption. apply (remc_ok c h). trivial. trivial.
Defined.

Definition hw_aux : forall b q s u a t h e,
  Pf b q s (state (u, a, t, h, e)) ->
  (length e) + (length h) <= s ->
  Pf b q s (winners (e ++ h)).
Proof.
  intros.
  apply (hw b q s (e++h) u a t h e).
  assumption. assumption. trivial.
Defined.

Definition ew_aux : forall b q s u a t h e,
  Pf b q s (state (u, a, t, h, e)) ->
  length e = s ->
  Pf b q s (winners e).
Proof.
  intros.  
  apply (ew b q s e u a t h e).
  assumption. assumption. trivial.
Qed.

(* miscellaneous lemmas about lists *)
Lemma length_3 : forall l1 l2 l3 : list cand, length (l1 ++ l2 ++ l3) = 
  ((length l1) + (length l2) + length l3)%nat.
Proof.
  intros l1 l2 l3.
  (* ++ is right associative *)
  transitivity (length l1 + (length (l2 ++ l3)))%nat.
  (* app_length: forall (A : Type) (l l' : list A), length (l ++ l') = (length l + length l')%nat *)
  apply (app_length l1 (l2 ++l3)).
  replace (length (l2 ++ l3)) with (length l2 + length l3)%nat.
  auto with arith. symmetry.
  apply (app_length l2 l3).
Qed.

(* pd and split *)
Lemma pd_split_aux {A:Type}: forall l0 l1 l: list A,
  l = l0 ++ l1 -> PD l -> (PD l0) /\ (PD l1).
Proof.
  intro l0. induction l0 as [|x xs IHxs].
  (* case l0 = [] *)
  intros l1 l eq pd.
  split. constructor.
  replace l1 with l; assumption.
  (* l0 = x::xs *)
  intros l1 l eq pd.
  replace l with (x::(xs++l1)) in pd.
  inversion pd as [fst  | fst l2 Hctr Heq ].
  destruct Hctr as [ pdxsl1 ninx ].
  specialize (IHxs l1 (xs ++ l1)).
  specialize (IHxs eq_refl).
  specialize (IHxs pdxsl1).
  assert (~ (In x xs)).
  intro inxxs. contradict ninx.
  (* in_or_app:
  forall (A : Type) (l m : list A) (a : A),
  In a l \/ In a m -> In a (l ++ m) *)
  apply (in_or_app xs l1). left. assumption.
  destruct IHxs as [ pdxs pdl1 ].
  split.
  apply (PDc x xs).
  split. assumption. assumption. assumption.
Qed.

Lemma pd_split_left {A: Type}: forall l0 l1: list A, 
  PD (l0 ++ l1) -> PD l0.
Proof.
  intros l0 l1 pd.
  assert (H: PD l0 /\ PD l1) by apply (pd_split_aux l0 l1 (l0 ++ l1) eq_refl pd).
  destruct H as [ Hl Hr ]. assumption.
Qed.

Lemma pd_split_right {A: Type}: forall l0 l1: list A,
  PD (l0 ++ l1) -> PD l1.
Proof.
  intros l0 l1 pd.
  assert (H: PD l0 /\ PD l1) by apply (pd_split_aux l0 l1 (l0 ++ l1) eq_refl pd).
  destruct H as [ Hl Hr ]. assumption.
Qed.

Lemma pd_split_3_aux {A: Type}: forall l0 l1 l2 l: list A,
  l = l0 ++ l1 ++ l2 -> PD l  -> PD (l0 ++ l2).
Proof.
  intro l0. induction l0 as [ | x xs IHxs].
  (* case l0 = [] *)
  intros l1 l2 l eq pd.
  replace l with (l1 ++ l2) in pd.
  replace ([] ++ l2) with l2.
  apply (pd_split_right l1 l2 pd). auto.
  (* case l0 = x::xs *)
  intros l1 l2 l eq pd.
  replace l with (x::(xs ++ l1 ++ l2)) in pd.
  inversion pd as [fst  | fst l3 Hctr Heq ].
  destruct Hctr as [ Hpd Hnin ].
  specialize (IHxs l1 l2 (xs ++ l1 ++ l2) eq_refl Hpd).
  replace ((x::xs) ++ l2) with (x::(xs ++ l2)).
  apply (PDc x (xs ++ l2)).
  split. assumption. contradict Hnin.
  (* in_app_or:
  forall (A : Type) (l m : list A) (a : A),
  In a (l ++ m) -> In a l \/ In a m *)
  assert (Hor: In x xs \/ In x l2) by apply (in_app_or xs l2 x Hnin).
  destruct Hor.
  apply (in_or_app xs (l1++l2) x). left. assumption.
  replace (xs ++ l1 ++ l2) with ( (xs ++ l1) ++ l2).
  apply (in_or_app (xs ++ l1) l2). right.  assumption.
  symmetry. apply (app_assoc xs l1 l2). auto.
Qed.

Lemma pd_split {A: Type}: forall l0 l1 l2: list A,
  PD (l0 ++ l1 ++ l2) -> PD (l0 ++ l2).
Proof.
  intros l0 l1 l2 pd.
  apply (pd_split_3_aux l0 l1 l2 (l0 ++ l1 ++ l2) eq_refl pd).
Qed.

Lemma pd_nin_aux {A: Type}: forall l0 l1 l: list A, forall c:A, 
  PD l -> l = l0 ++ [c] ++ l1 -> ~(In c (l0 ++ l1)).
Proof.
  intros l0. induction l0 as [ | x xs IHxs ].
  (* l0 = [] *)
  intros l1 l c pd eq.
  replace ([] ++ l1) with l1.
  replace ([] ++ [c] ++ l1) with (c::l1).
  replace l with (c::l1) in pd.
  inversion pd as [fst  | fst l2 Hctr Heq ].
  destruct Hctr as [H0 H1].
  assumption.
  auto. auto.
  (* l0 = x::xs *)
  intros l1 l c pd eq.
  replace ( (x::xs) ++ [c] ++ l1) with (x::(xs ++ [c] ++ l1)) in eq.
  replace l with (x::(xs ++ [c] ++ l1)) in pd.
  inversion pd as [fst  | fst l2 Hctr Heq ].
  destruct Hctr as [H1 H2].
  specialize (IHxs l1 (xs ++ [c] ++ l1) c H1 eq_refl).
  replace  ( (x::xs) ++ l1) with (x::(xs ++ l1)).
  intro nin.
  specialize (in_inv nin).
  intro d.
  destruct d.
  contradict H2.
  replace c with x.
  specialize (in_or_app xs (x::l1) x).
  intros H2. apply H2. right. apply (in_eq x l1). contradict IHxs.
  assumption. auto. auto.
Qed.

Lemma pd_nin {A: Type}: forall l0: list A, forall c: A, forall l1: list A,
  PD (l0 ++ [c] ++ l1) -> ~ (In c (l0 ++ l1)).
Proof.
  intros l0 c l1 pd.
  apply (pd_nin_aux l0 l1 (l0 ++ [c] ++ l1) c pd eq_refl).
Qed.

Lemma pd_ins_pd {A: Type}: forall l: list A,
  PD l -> forall c nl, eqe c nl l -> PD nl.
Proof.
  intros l pd c nl H.
  unfold eqe in H.
  destruct H as [l1 H].
  destruct H as [l2 H].
  destruct H as [S1 S2].
  replace l with (l1 ++ [c] ++ l2) in pd.
  replace nl with (l1 ++ l2).
  apply (pd_split l1 [c] l2 pd).
Qed.

Lemma pd_ins_nin {A: Type}: forall l: list A, forall c: A, forall nl: list A,
  eqe c nl l -> PD l -> ~(In c nl).
Proof.
  intros l c nl H pd.
  unfold eqe in H. 
  destruct H as [l1 H]. destruct H as [l2 H]. destruct H as [S1 S2].
  replace l with (l1 ++ [c] ++ l2) in pd. replace nl with (l1 ++ l2).
  apply (pd_nin l1 c l2 pd).
Qed.

Lemma pd_remc_nin: forall l c, In c l -> PD l -> ~ (In c (remc c l)).
Proof.
  intros l c H pd.
  assert (eqe c (remc c l) l) by apply (remc_ok c l H).
  apply (pd_ins_nin l c (remc c l) H0 pd).
Qed.

(* removing an element doesn't increase list length *)
Lemma rem_length : forall c:cand, forall l: list cand,
  (length (remc c l)) <= length l.
Proof.
  intro c.
  induction l. compute. auto.
  assert (H: {c=a} + {c <> a}) by apply (cand_eq_dec c a). destruct H as [ceqa | cneqa].
  replace (remc c (a::l)) with l.
  replace (length (a::l)) with (S (length l)). auto with arith. auto.
  unfold remc. destruct (cand_eq_dec c a). trivial. contradict n. assumption.
  replace (remc c (a::l)) with (a::(remc c l)).
  transitivity (S (length (remc c l))). auto. transitivity (S (length l)). omega.
  auto. unfold remc. destruct (cand_eq_dec c a). contradict cneqa. assumption. trivial.
Qed.

Lemma rem_in_length: forall l c, In c l -> (1 + length (remc c l))%nat = (length l).
Proof.
  intro l. induction l as [ | l0 ls IHl].
  intros c incemp. contradict incemp.
  intros c inc.
  assert ({c=l0} + {c <> l0}) by apply (cand_eq_dec c l0).
  destruct H as [ceql0 | cneql0].
  (* case c = l0 *)
  replace l0 with c.
  replace (remc c (c::ls)) with ls.
  replace (length (c::ls)) with (1 + (length ls))%nat.
  auto with arith. auto. unfold remc. destruct (cand_eq_dec c c). trivial. contradict n. trivial.
  assert (l0 = c \/ In c ls).
  apply (in_inv inc).
  destruct H. contradict cneql0. symmetry. assumption.
  replace (remc c (l0::ls)) with (l0:: remc c ls).
  replace (length (l0:: remc c ls)) with (1 + length (remc c ls))%nat.
  replace (length (l0::ls)) with (1 + length ls)%nat.
  replace (1 + length (remc c ls))%nat with (length ls).
  trivial.
  symmetry.
  apply (IHl c H). auto. auto. unfold remc.
  destruct (cand_eq_dec c l0). contradict cneql0. assumption. trivial.
Qed.

Lemma rem_in_length_leq: forall l: list cand, forall c:cand, In c l ->
  length (remc c l) < length l.
Proof.
  intros l c i.
  replace (length l) with (1 + length (remc c l))%nat.
  auto with arith.
  apply (rem_in_length l c i).
Qed.

Lemma in_rem : forall l c d, In d (remc c l) -> In d l.
Proof.
  intro l. induction l.
  intros c d i. contradict i.
  intros c d i.
  unfold remc in i. destruct (cand_eq_dec c a).
  (* in_cons: forall (A : Type) (a b : A) (l : list A), In b l -> In b (a :: l) *)
  apply (in_cons a d l i).
  assert (j: In d (a::remc c l)). unfold remc. assumption.
  specialize (in_inv j). intro H. destruct H.
  replace a with d.
  (* in_eq
     : forall (A : Type) (a : A) (l : list A), In a (a :: l) *)
  apply (in_eq d l).
  specialize (in_inv j). intro H1. destruct H1 as [H1 | H2].
  replace a with d.
  apply (in_eq d l).
  specialize (IHl c d H2).
  (* in_cons: forall (A : Type) (a b : A) (l : list A), In b l -> In b (a :: l) *)
  apply (in_cons a d l IHl).
Qed.

(* we can find a candidate with least no of first prefs *)
Lemma list_min : forall A:Type, forall l: list A, forall f: A -> nat,
   (l = []) + (existsT m:A, (In m l /\ (forall b:A, In b l ->f m <= f b))).
Proof.
  intros.
  induction l as [ | l ls ].
  left. trivial.
  destruct IHls.
  right.
  exists l. split.
  apply (in_eq l ls). intros b ass.
  assert (l = b \/ In b ls).
  apply (in_inv ass). destruct H. replace l with b. apply (le_n (f b)). replace ls with ([] : list A) in H.
  contradict H.
  right. destruct s. destruct a.
  assert ( {f x <= (f l)}  + {(f l) <= (f x)}).
  apply (le_ge_dec (f x) (f l)). destruct H1.
  (* x is the minimum *)
  exists x. split.
  apply (in_cons l x ls). assumption. intros b ass.
  assert (l = b \/ In b ls).
  apply (in_inv ass).
  destruct H1. replace b with l. assumption.
  apply (H0  b H1).
  (* l is the minimum *)
  exists l. split.
  apply (in_eq l ls).
  intros b ass.
  assert (l = b \/ In b ls). apply (in_inv ass). destruct H1. 
  replace l with b. apply (le_n (f b)).
  transitivity (f x). assumption. apply (H0 b). assumption.
Defined.

(* invariants of STV counting *)
(* throughout the count, we never elect more cands than seats *)
Lemma els_lt_seats_aux: forall b q s x,
  Pf b q s x -> 
  forall u a t h e, x = state (u, a, t, h, e) ->
  length e <= s.
Proof.
  intros b q s x p.
  induction p as [u a t h e d i he1 he2 he3 he4 | 
                  u nu a na t nt h e f fs p IH hjn hin hum hadd hinc hleq |
                  u a t h nh e ne c p IH hin hlen heq hjh hje |
                  u nu a t h e f fs p IH hnin hrep |
                  u nu  a t h e p IH hju |
                  u a t h nh e c p IH hlen hin hleq hju ha |
                  w u a t h e p IH hlen heq |
                  w u a t h e p IH hlen heq ].
  (* axiom *)
  intros.
  replace e0 with nbdy. compute. apply (Le.le_0_n s).
  transitivity e. auto. injection H. intros. assumption.
  (* count one *)
  intros u0 a0 t0 h0 e0 heq.
  replace e0 with e.
  apply (IH u a t h e). trivial. injection heq. intros. assumption.
  (* elect *)
  intros u1 a1 t1 h1 e1 eq.
  unfold eqe in hje. destruct hje as [l1  hje ]. destruct hje as [l2 hje].
  replace e1 with (l1 ++ [c] ++ l2).
  replace (length (l1 ++ [c] ++ l2)) with ((length l1) + (length [c]) + (length l2))%nat.
  replace (length [c]) with 1.
  replace ((length l1) + 1 + (length l2))%nat with ((length l1) + (length l2) + 1)%nat.
  replace ((length l1) + (length l2))%nat with (length (l1 ++ l2))%nat.
  replace (l1 ++ l2) with e.
  replace ( (length e) + 1)%nat with (S (length e)).
  (* Gt.gt_le_S: forall n m : nat, m > n -> S n <= m *)
  apply (Gt.gt_le_S (length e) s). trivial. omega.
  destruct hje as [hje1 hje2]. assumption.
  (* app_length: forall (A : Type) (l l' : list A), length (l ++ l') = (length l + length l')%nat *)
  apply (app_length l1 l2). omega. auto.
  symmetry. apply (length_3 l1 [c] l2).
  transitivity ne. symmetry. destruct hje as [hje1 hje2]. assumption.
  injection eq; intros; assumption.
  (* transfer vote *)
  intros u0 a0 t0 h0 e0 eq.
  replace e0 with e.
  apply (IH u a t h e).
  trivial. injection eq. intros. assumption.
  (* empty vote *)
  intros u0 a0 t0 h0 e0 eq.
  replace e0 with e.
  apply (IH u a t h e). trivial.
  injection eq. intros. assumption.
  (* transfer least *)
  intros u0 a0 t0 h0 e0 eq.
  replace e0 with e.
  apply (IH ([]: list ballot) a t h e). trivial.
  injection eq. intros. assumption.
  (* hopefuls win *)
  intros. discriminate H.
  (* elected win *)
  intros. discriminate H.
Qed.

Lemma els_lt_seats: forall b q s u a t h e,
  Pf b q s (state (u, a, t, h, e)) ->  (length e) <= s.
Proof.
  intros b q s u a t h e p.
  specialize (els_lt_seats_aux b q s (state (u, a, t, h, e))).
  intro H.
  specialize (H p).
  specialize (H u a t h e).
  apply H. trivial.
Qed.

(* throughout the count, the hopefuls are always pairwise distinct *)
Lemma pd_hop_aux : forall b q s n, Pf b q s n ->
  forall u a t h e, n = state (u, a, t, h, e) -> PD h.
Proof.
  intros b q s n p.
  induction p as [u a t h e d i he1 he2 he3 he4 | 
                  u nu a na t nt h e f fs p IH hjn hin hum hadd hinc hleq |
                  u a t h nh e ne c p IH hin hlen heq hjh hje |
                  u nu a t h e f fs p IH hnin hrep |
                  u nu  a t h e p IH hju |
                  u a t h nh e c p IH hlen hin hleq hju ha |
                  w u a t h e p IH hlen heq |
                  w u a t h e p IH hlen heq ].
  (* axiom *)
  intros. 
  replace h0 with h. assumption.
  injection H. intros. assumption.
  (* count one *)
  intros u0 a0 t0 h0 e0 heq.
  replace h0 with h.
  apply (IH u a t h e). trivial. injection heq; intros; assumption.
  (* elect *)
  intros u1 a1 t1 h1 e1 eq.
  replace h1 with nh.
  assert (pdh: PD h).
  apply (IH u a t h e). trivial.
  apply (pd_ins_pd h pdh c nh). assumption. injection eq. intros. assumption.
  (* transfer vote *)
  intros u0 a0 t0 h0 e0 eq.
  specialize (IH u a t h e eq_refl).
  replace h0 with h. assumption. injection eq; intros; assumption.
  (* empty vote *)
  intros u0 a0 t0 h0 e0 eq.
  specialize (IH u a t h e eq_refl).
  replace h0 with h. assumption. injection eq; intros; assumption.
  (* transfer least *)
  intros u0 a0 t0 h0 e0 eq.
  specialize (IH ([]: list ballot) a t h e eq_refl).
  replace h0 with nh.
  apply (pd_ins_pd h IH c nh). assumption. injection eq; intros; assumption.
  (* hopefuls win *)
  intros. discriminate H.
  (* elected win *)
  intros. discriminate H.
Qed.

Lemma pd_hop: forall b q s u a t h e, Pf b q s (state (u, a, t, h, e)) -> PD h.
Proof.
  intros.
  pose (n := state (u, a, t, h, e)).
  apply (pd_hop_aux b q s n X u a t h e eq_refl).
Qed.

Lemma lt_quota_aux : forall b q s n, Pf b q s n -> forall u a t h e,
  n  = state (u, a, t, h, e) -> forall c, t c <= q.
Proof.
  intros b q s n p.
  induction p as [u a t h e d i he1 he2 he3 he4 | 
                  u nu a na t nt h e f fs p IH hjn hin hum hadd hinc hleq |
                  u a t h nh e ne c p IH hin hlen heq hjh hje |
                  u nu a t h e f fs p IH hnin hrep |
                  u nu  a t h e p IH hju |
                  u a t h nh e c p IH hlen hin hleq hju ha |
                  w u a t h e p IH hlen heq |
                  w u a t h e p IH hlen heq ].
  (* ax *)
  intros u0 a0 t0 h0 e0 eq c.
  replace t0 with nty. unfold nty. auto with arith.
  transitivity t. symmetry. assumption. injection eq; intros; assumption.
  (* c1 *)
  intros u0 a0 t0 h0 e0 eq.
  assert (forall c, t c <= q).
  apply (IH u a t h e).
  trivial.
  replace t0 with nt.
  intro c.
  unfold inc in hinc.
  destruct hinc as [hinc1 hinc2].
  assert ( H0: {c = f} + {c <> f}) by apply cand_eq_dec.
  destruct H0 as [ eqf | neqf ].
  (* case c = f *)
  replace c with f.
  replace (nt f) with (t f + 1)%nat. omega.
  (* case c <> f *)
  replace (nt c) with (t c). apply (H c).
  symmetry.
  apply (hinc2 c). assumption.
  injection eq; intros; assumption.
  (* el *)
  intros u0 a0 t0 h0 e0 eq.
  assert (forall c, t c <= q).
  apply (IH u a t h e). trivial.
  replace t0 with t. assumption.
  injection eq; intros; assumption.
  (* tv *)
  intros u0 a0 t0 h0 e0 eq.
  assert (forall c, t c <= q).
  apply (IH u a t h e). trivial.
  replace t0 with t. assumption.
  injection eq; intros; assumption.
  (* ey *)
  intros u0 a0 t0 h0 e0 eq.
  assert (forall c, t c <= q).
  apply (IH u a t h e). trivial. 
  replace t0 with t.  assumption.
  injection eq; intros; assumption.
  (* tl *)
  intros u0 a0 t0 h0 e0 eq.
  assert (forall c, t c <= q).
  apply (IH ([]: list ballot) a t h e). trivial.
  replace t0 with t. assumption.
  injection eq; intros; assumption.
  (* ew *)
  intros u0 a0 t0 h0 e0 eq.
  discriminate eq.
  (* hw *)
  intros u0 a0 t0 h0 e0 eq.
  discriminate eq.
Qed.

Lemma lt_quota : forall b q s u a t h e, Pf b q s (state (u, a, t, h, e)) ->
  forall c, t c <= q.
Proof.
  intros b q s u a t h e p.
  specialize (lt_quota_aux b q s (state (u, a, t, h, e)) p).
  intro ass.
  specialize (ass u a t h e).
  apply ass. trivial.
Qed.

(* election progress *)
(* termination *)
Lemma close_aux: forall b q s u a t h e,
  Pf b q s (state (u, a, t, h, e)) ->
  (existsT w, Pf b q s (winners w)) +
  (length e < s) * (length e + length h > s).
Proof.
  intros b q s u a t h e p.
  (* if we have fewer hopefuls than seats available, we can close *)
  (* Compare_dec.le_gt_dec: forall n m : nat, {n <= m} + {n > m} *)
  assert (cl: {(length e + length h) <= s} + {length e + length h > s}).
  apply (Compare_dec.le_gt_dec (length e + length h) s).
  destruct cl.
  (* case fewer hopefuls than free seats *)
  left. exists (e ++ h). apply (hw b q s (e++h) u a t h e).
  assumption. assumption. trivial.
  (* if we have as many elected candidates as seats, we can close *)
  assert (cl: {s <= length e} + {s > length e}).
  apply (Compare_dec.le_gt_dec s (length e)).
  destruct cl.
  assert (eq: s = length e).
  (* Le.le_antisym: forall n m : nat, n <= m -> m <= n -> n = m *)
  apply (Le.le_antisym s (length e)).
  assumption.
  apply (els_lt_seats b q s u a t h e p).
  left. exists e. 
  apply (ew b q s e u a t h e). assumption. auto. trivial.
  (* in all other cases we cannot close *)
  right. split. auto. auto.
Defined.

(* reduction of hopefuls *)
Lemma red_h: forall n b q s u a t h e, n = length h ->
  Pf b q s (state (u, a, t, h, e)) ->
  (forall c, In c h -> t c < q) ->
  (existsT w, Pf b q s (winners w)) +
    (existsT nu na nt nh ne, Pf b q s (state (nu, na, nt, nh, ne)) * (forall c, In c nh -> nt c < q) * (length nh < length h)).
Proof.
  intros n b q s. induction n.
  (* no hopefuls *)
  intros u a t h e len p sober.
  destruct h as [ | h0 hs].
  left. exists (e ++ []).
  apply (hw_aux b q s u a t [] e).
  assumption.
  replace (length []) with 0.
  replace (length e + 0)%nat with (length e).
  apply (els_lt_seats b q s u a t [] e p).
  auto with arith.
  (* case h = h0::hs: contradicts length h = 0 *)
  replace (length (h0::hs)) with (S (length hs)) in len.
  contradict len. auto with arith. auto.
  (* length h = n > 0 *)
  (* induction on oncounted ballots *)
  intro u. induction u as [ | u0 us IHus].
  (* case no uncounted ballots *)
  intros a t h e len p sober.
  (* can we close already? *)
  assert (H: (existsT w, Pf b q s (winners w)) +
    (length e < s) * (length e + length h > s)).
  apply (close_aux b q s [] a t h e p).
  destruct H as [cl | nyet].
  (* we can close *)
  left. assumption.
  (* we cannot close yet *)
  destruct nyet as [n1 n2].
  assert (H: (h=[]) + (existsT c, In c h /\ forall d, In d h -> t c <= t d)).
  apply (list_min cand h t).
  destruct H as [hnil | hnnil].
  replace h with ([]: list cand) in len.
  replace (length []) with 0 in len.
  contradict len. auto. auto.
  destruct hnnil as [c min].
  (* c is a cand with minimal no of first prefs. eliminate *)
  assert (p0: Pf b q s (state (a c, a, t, remc c h, e))).
  apply (tl_aux b q s a t h e c p).
  assumption. destruct min as [m1 m2]. assumption. destruct min as [m1 m2].
  assumption.
  assert (1 + length (remc c h) = length h)%nat.
  apply (rem_in_length h c).
  destruct min. assumption.
  replace (length h) with (S n) in H.
  assert (length (remc c h) = n).
  omega.
  specialize (IHn (a c) a t (remc c h) e).
  assert (H1: n = length (remc c h)).
  symmetry. assumption.
  specialize (IHn H1). specialize (IHn p0).
  destruct min as [m1 m2].
  assert (H2: forall d, In d (remc c h) -> t d < q).
  intro d.
  assert (forall d, In d (remc c h) -> t d < q).
  intro d0. intro ass.
  apply (sober d0).
  apply (in_rem h c d0). assumption.
  apply (H2 d).
  specialize (IHn H2).
  destruct IHn as [ win | nyet ].
  left. assumption.
  right.
  destruct nyet as [ nu nyet]. destruct nyet as [na nyet].
  destruct nyet as [nt nyet]. destruct nyet as [nh nyet].
  destruct nyet as [ne nyet].
  destruct nyet as [i0 i1]. destruct i0 as [i0 i3].
  exists nu. exists na. exists nt. exists nh. exists ne.
  split. split. assumption.
  assumption.
  replace (length h) with (S n). omega.
  (* case uncounted ballots of the form u0::us *)
  intros a t h e len p sober.
  (* can we close already? *)
  assert (H: (existsT w, Pf b q s (winners w)) +
  (length e < s) * (length e + length h > s)).
  apply (close_aux b q s (u0::us) a t h e p).
  destruct H as [cl | nyet].
  (* we can close *)
  left. assumption.
  (* we cannot close. induction on first uncounted vote *)
  destruct nyet as [i0 i1].
  induction u0 as [ | f fs IHfs].
  (* empty first vote: ignore *)
  assert (p0: Pf b q s (state (us, a, t, h, e))).
  apply (ey_aux b q s us a t h e). assumption.
  specialize (IHus a t h e len p0).
  specialize (IHus sober). assumption.
  (* first vote of the form f::fs *)
  (* is f a hopeful? *)
  assert (H: {In f h} + {~(In f h)}).
  (* forall A : Type,
       (forall x y : A, {x = y} + {x <> y}) -> forall (a : A) (l : list A), {In a l} + {~ In a l} *)
  apply (in_dec cand_eq_dec f h).
  destruct H as [fhop | fnhop].
  (* f is a hopeful *)
  (* count the vote for f *)
  assert (p0: Pf b q s (state (us, adda f (f::fs) a, inct f t, h, e))).
  apply (c1_aux b q s f fs us a t h e p).
  assumption.
  apply (sober f). assumption.
  (* if f has enough votes, f can be seated *)
  (* le_lt_dec: forall n m : nat, {n <= m} + {m < n} *)
  assert ({q <= inct f t f} + {inct f t f < q}) by apply (le_lt_dec q (inct f t f)).
  destruct H as [nuff | nnuff ].
  (* f has >= q votes. Need exact number of votes *)
  assert (inct f t f <= q) by apply (lt_quota b q s us (adda f (f::fs) a) (inct f t) h e p0).
  assert (exact: inct f t  f= q) by omega.
  assert (p1: Pf b q s (state (us, adda f (f::fs) a, inct f t, remc f h, f::e))).
  apply (el_aux b q s us (adda f (f::fs) a) (inct f t) h e f p0).
  assumption. assumption. assumption.
  (* now have a proof where f was seated. the tally of all others should be below q still *)
  (* to appy IH, we need that there's one less hopeful *)
  assert (nhop: n = length (remc f h)).
  symmetry.
  apply (eq_add_S (length (remc f h)) n).
  replace (S n) with (length h).
  replace (S (length (remc f h))) with (1 + length (remc f h))%nat.
  apply (rem_in_length h f fhop). auto.
  (* we also need that the new proof is sober *)
  assert (ss : forall c, In c (remc f h) -> (inct f t) c < q).
  intros c Hin.
  unfold inct.
  destruct (cand_eq_dec f c).
  (* we have f = c which is impossible as In c (remc f h) *)
  assert (pdhop: PD h).
  apply (pd_hop b q s ((f::fs)::us) a t h e p).
  contradict Hin.
  replace c with f.
  apply (pd_remc_nin h f fhop pdhop).
  (* now for f <> c *)
  assert (infh: In c h).
  apply (in_rem h f c Hin).
  apply (sober c infh).
  (* attach the induction hypothesis *)
  specialize (IHn us (adda f (f::fs) a) (inct f t) (remc f h) (f::e) nhop p1 ss).
  (* the IH tells us that we have winners or the invariant *)
  destruct IHn as [win | nyet].
  left. assumption.
  (* pull IH apart to establish conclusion *)
  destruct nyet as [nu nyet]. destruct nyet as [na nyet].
  destruct nyet as [nt nyet]. destruct nyet as [nh nyet]. 
  destruct nyet as [ne nyet]. destruct nyet as [P0 P1]. destruct P0 as [P0 P2].
  right. exists nu. exists na. exists nt. exists nh. exists ne.
  split. split. assumption.
  (* establish the invariants *)
  assumption.
  transitivity n.
  replace n with (length (remc f h)). assumption.
  replace (length h) with (S n). auto with arith.
  (* case where f doesn't have enough votes to be seated (but is hopeful) *)
  (* need that the p0 is sober *)
  assert (ss: forall c, In c h -> inct f t c < q).
  intros c Hin. unfold inct. destruct (cand_eq_dec f c).
  replace c with f. replace (S (t f ))%nat with (inct f t f). assumption.
  unfold inct. destruct (cand_eq_dec f f). trivial. contradict n0. trivial.
  apply (sober c Hin).
  specialize (IHus  (adda f (f::fs) a)  (inct f t) h e len p0 ss).
  assumption.
  (* case f is not a hopeful *)
  assert (p0: Pf b q s (state (fs::us, a, t, h, e))) by apply (tv_aux b q s f fs us a t h e p fnhop).
  specialize (IHfs p0). assumption.
Defined.

Lemma str_aux: forall p:nat -> Type, 
  (forall n : nat, (forall k : nat, (k < n -> p k)) -> p n) ->
  forall n : nat, forall k:nat, k <= n -> p k.
Proof.
  intros p H. induction n as [ | n IHn ].
  intro k. intro leq0.
  assert (k = 0). omega. replace k with 0. apply (H 0).
  intro k0. intro ass. contradict ass. auto with arith.
  (* case S n *)
  intros k ass.
  apply (H k). intros k0 ass2.
  apply (IHn k0).
  omega.
Defined.

Theorem str_ind:forall p : nat -> Type,(forall n : nat, (forall k : nat, (k < n -> p k)) -> p n) ->forall n : nat, p n.
Proof.
  intros p H n.
  assert (H0: forall k:nat, k <= n -> p k).
  apply (str_aux p H).
  apply (H0 n).
  auto.
Defined.
 

Lemma ex_winners_pf_aux: forall n:nat,
  forall b q s u a t h e, n = length h ->
  Pf b q s (state (u, a, t, h, e)) ->
  (forall c, In c h -> t c < q) ->
  existsT w: list cand, Pf b q s (winners w).
Proof.
  intro n.
  (* well-founded induction on n *)
  induction n as [ n IH ] using str_ind.
  intros b q s u a t h e en p sob.
  assert (H0: (existsT w, Pf b q s (winners w)) +
    (existsT nu na nt nh ne, Pf b q s (state (nu, na, nt, nh, ne)) * (forall c, In c nh -> nt c < q) * (length nh < length h))).
  apply (red_h n b q s u a t h e en p sob).
  destruct H0 as [win | nyet]. assumption.
  destruct nyet as [nu nyet]. destruct nyet as [na nyet].
  destruct nyet as [nt nyet]. destruct nyet as [nh nyet]. 
  destruct nyet as [ne nyet]. destruct nyet as [P0 P1]. destruct P0 as [P0 P2].
  replace (length h) with n in P1.
  apply (IH (length nh)  P1 b q s nu na nt nh ne (eq_refl) P0 P2).
Defined.

Theorem ex_winners_pf: forall b q s, q > 0 ->
  existsT w: list cand, Pf b q s (winners w).
Proof.
  intros b q s qpos.
  assert (p: Pf b q s (state (b, nas, nty, cand_all, nbdy))).
  apply (ax_aux b q s).
  assert (sob: forall c, In c cand_all -> nty c < q).
  intro c. intro H. unfold nty. omega.
  apply (ex_winners_pf_aux (length cand_all) b q s b nas nty cand_all nbdy eq_refl p sob).
Defined.

End STV.

Section candidates.
(* our candidates *)
Inductive cand := Alice | Bob | Charlie | Deliah.
Definition cand_all := [Alice; Bob; Charlie; Deliah].

(* everything below here is independent of the definition of cand *)
(* as long as cand is an inductive type with nullary constructors *)
(* only and all_cands mentions all of them.                       *)

Lemma cand_pd: PD cand_all.
Proof.
  repeat apply PDc
    || split
    || (repeat apply PDe
        || unfold In
        || tauto
        || (intro H; discriminate H; clear H)
        || (intro H; elim H; clear H)).
Qed.

Lemma cand_finite: forall c, In c cand_all.
Proof.
  unfold cand_all; intro a; repeat induction a || (unfold In; tauto).
Qed.

Lemma  cand_eq_dec : forall c d : cand, {c = d} + {c <> d}.
Proof.
  intros a b;
  repeat induction a; 
    repeat (induction b) || (right; discriminate) ||(left; trivial).
Defined.

End candidates.

(* instantiation and extraction of counting *)
Definition cand_ex_winners_pf :=
  ex_winners_pf cand cand_all cand_pd cand_finite cand_eq_dec.

Extraction Implicit c1 [u a t f fs].
Extraction Implicit el [h e c].
Extraction Implicit tv [u f fs].
Extraction Implicit ey [u].
Extraction Implicit tl [h c].
Extraction Implicit hw [u a t h e].
Extraction Implicit ew [u a t h e].

Extraction Language Haskell.
Extraction "STVCode" cand_ex_winners_pf.


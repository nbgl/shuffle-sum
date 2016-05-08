Require Import Coq.Lists.List.
Require Import Coq.Init.Datatypes.
Import ListNotations.
Section STV.
Require Export Arith.

Variable cand: Type.
Definition cand_eq : cand -> cand -> bool. Admitted.
Definition ballot := (nat * (list cand)) % type.

Inductive Node :=
    state:                     (** intermediate states  **)
       (list ballot)           (*  undistributed ballots *)
     * nat                     (*  remaining seats       *)
     * (list cand)             (*  hopeful candidates    *)
     * (cand -> (list ballot)) (*  piles                 *)
     * (cand -> nat)           (*  tallies               *)
     * (list cand)             (*  elected candidates    *)
     -> Node
  | winners:                   (** final state          **)
       list cand
     -> Node.                  (*  election winners      *)

(* shorthands *)
Definition nbdy : list cand := [].                    (* empty candidate list *)
Definition nty  : cand -> nat := fun x => 0.          (* null tally *)
Definition nas  : cand -> list ballot := fun x => []. (* null vote assignment *)

Inductive PD  {A: Type} : list A -> Prop :=
   PDe :  PD  ( nil)
 | PDc :  forall a:A,forall l: list A, PD l /\ ~(In a l) -> (PD  (cons a l)).

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

Fixpoint index (l : list cand) (c : cand) : option nat :=
  match l with
  | []      => None
  | c' :: l' =>
    if cand_eq c c' then Some 0
    else
      match index l' c with
      | None   => None
      | Some n => Some (S n)
      end
  end.

Definition bweight (b: ballot) : nat :=
  match b with
  | (w, _) => w
  end.

Definition blist (b: ballot) : list cand :=
  match b with
  | (_, l) => l
  end.

Definition unpack (i: option nat) (d: nat) : nat :=
  match i with
  | Some j => j
  | None => d
  end.

Definition multiply_weight (i: nat) (b: ballot) : ballot :=
  match b with
  | (j, l) => (i * j, l)
  end.

Inductive Pf (b: list ballot) (q: nat) (s: nat) : Node -> Type := 
  ax : forall u r h p t e,                           (** start counting                                                **)
  u = b ->                                           (*  if all the ballots are unallocated                             *)
  r = s ->                                           (*  if all the seats are vacant                                    *)
  PD h  ->                                           (*  if all hopeful candidates are unique                           *)
  p = nas ->                                         (*  if all piles are empty                                         *)
  t = nty ->                                         (*  all tallies are zero                                           *)
  e = nbdy ->                                        (*  nobody has been elected                                        *)
  Pf b q s (state (u, r, h, p, t, e))
| db : forall u r h p t e   un pn,                   (** distribute ballots to piles                                   **)
  Pf b q s (state (u, r, h, p, t, e)) ->             (*  if at any time                                                 *)
  u <> [] ->                                         (*  there are votes to distribute                                  *)
  (forall i : ballot, (In i u) ->                    (*  each ballot is assigned to at least one pile of a hopeful      *)
    (exists (j : cand), (In j h)                     (*    candidate                                                    *)
                        /\ (In i (pn j)))) ->
  (forall (i : cand) (l : ballot), (In i h) ->       (*  ensure that candidate is first amongst hopefuls for each       *)
    (forall (j : cand), (In j h) -> unpack (index (blist l) j) 0 (*    ballot on their pile                                         *)
      >  unpack (index (blist l) i) 0) -> (In l (p i))) ->
  un = [] ->                                         (*  the undistributed ballots list is empty                        *)
  Pf b q s (state (un, r, h, pn, t, e))
| tv : forall u r h p t e   tn,                      (** tally votes                                                   **)
  Pf b q s (state (u, r, h, p, t, e)) ->             (*  if at any time                                                 *)
  t = nty ->                                         (*  the tally is empty                                             *)
  u = []  ->                                         (*  there are no undistributed ballots                             *)
  (forall i : cand, (In i h) ->                      (*  the tally for a candidate is the count of their pile weighted  *)
    tn i = fold_left (fun x y => x + y)              (*  by the weight of the ballots                                   *)
                     (map bweight (p i))
                     0) ->
  Pf b q s (state (u, r, h, p, tn, e))
| el : forall u r h p t e  un rn hn pn tn en  is iss,(** elect a candidate and redistribute their votes                **)
  Pf b q s (state (u, r, h, p, t, e)) ->             (*  if at any time                                                 *)
  (forall i : cand, In i is -> t i >= 1) ->          (*  a number of candidates meet the quota                          *)
  (forall i : cand,                                  (*  the elected candidates are removed from the hopefuls list      *)
    (In i is) /\ (In i h) = (In i hn)) ->  
  (forall i : cand,                                  (*  the elected candidates are added to the elected list           *)
    (In i is) \/ (In i e) = (In i en)) ->  
  tn = nty ->                                        (*  the tally is emptied                                           *)
  rn = r - 1 ->                                      (*  the number of remaining seats is reduced by one                *)
  (forall i: cand, (In i h) -> eqe i (iss i) is) ->
  un = fold_left                                     (*  the elected candidate's pile is redistributed.                 *)
       (fun x y => x ++ y)                           (*    with transfer value                                          *)
       (map (fun i => map (multiply_weight 
                           (fold_left
                            (fun x y => x * y)
                            (map t (iss i))
                            1))
                           (p i))
        is)
       [] -> 
  (forall i: cand, In i h ->                         (*  scale other piles with transfer value                         *)
    pn i = map (multiply_weight
                (fold_left (fun x y => x * y)
                           (map t is)
                           1))
               (p i)) ->
  Pf b q s (state (un, rn, hn, pn, tn, en)) 
| em : forall u r h p t e   un hn tn   i,            (** eliminate a candidate                                         **)
  Pf b q s (state (u, r, h, p, t, e)) ->             (*  if at any time                                                 *)
  r > length h ->                                    (*  there are more hopefuls than remaining seats                   *)
  t <> nty ->                                        (*  the votes have been tallied                                    *)
  (forall i : cand, (In i h) -> (t i) < q) ->        (*  no hopeful candidate meets the quota                           *)
  un = p i ->                                        (*  the eliminated candidate's pile is to be redistributed         *)
  eqe i hn h ->                                      (*  the eliminated candidate is removed from the hopefuls list     *)
  tn = nty ->                                        (*  empty the tallies                                              *)
  Pf b q s (state (un, r, hn, p, tn, e))
| ew : forall u r h p t e   w,                       (** elected win                                                   **)
  Pf b q s (state (u, r, h, p, t, e)) ->             (*  if at any time                                                 *)
  length h <= r ->                                   (*  we have as many seats as hopeful candidates                    *)
  w = e ++ h ->                                      (*  the winners are the already elected and the remaining hopefuls *)
  Pf b q s (winners w).



Definition encrypt : nat -> nat. Admitted.
Definition decrypt : nat -> nat. Admitted.
Theorem encrypt_inverse : forall (n : nat), encrypt(decrypt n) = n. Admitted.
Theorem decrypt_inverse : forall (n : nat), decrypt(encrypt n) = n. Admitted.

Definition h_add : nat -> nat -> nat. Admitted.
Theorem h_add_homomorphism : forall (n m : nat), h_add (encrypt n) (encrypt m) = encrypt (n + m). Admitted.

Definition first_pref_column := (nat   (* candidate index, plaintext *)
                                 * nat (* preference, encrypted      *)
                                 * nat (* weight, encrypted          *)
                                ) % type.
Definition first_preference_ballot := list first_pref_column.

Inductive SS_Node :=
    sstate:                            (** intermediate states             **)
       (list first_preference_ballot)  (*  first-preference representation  *)
     * (list nat)                      (*  hopefuls                         *)
     * (nat -> nat)                    (*  tallies                          *)
     -> SS_Node
  | swinners:                          (** final state                     **)
       (list cand)
     -> SS_Node.                         (*  election winners                 *)


Definition fpc_cand : first_pref_column -> nat. Admitted.
Definition fpc_weight : first_pref_column -> nat. Admitted.

Definition h_add_weights_b (c : nat) (b : first_preference_ballot)  : nat :=
  fold_left h_add
            (map fpc_weight (filter
                             (fun x : first_pref_column => beq_nat (fpc_cand x) c)
                             b))
            (encrypt 0).

Definition h_add_weights (b : list first_preference_ballot) (c : nat) : nat :=
  fold_left h_add
            (map (h_add_weights_b c) b)
            (encrypt 0).

Inductive Pfss (b: list ballot) (q: nat) (s: nat) : SS_Node -> Type :=
  ft : forall f h t  tn, (** compute first preference tallies **)
  Pfss b q s (sstate (f, h, t)) ->
    (forall i : nat, (In i h) -> tn i = decrypt (h_add_weights f i)) ->
  Pfss b q s (sstate (f, h, tn)).


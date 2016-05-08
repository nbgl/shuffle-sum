Require Import Coq.Lists.List.
Import ListNotations.

Section STV.

Variable cand: Type.
Definition ballot := list cand.

Inductive Node :=
   state:                     (** intermediate states **)
       (list ballot)            (* uncounted votes *)
     * nat                    (* remaining seats *)
     * (list cand)            (* hopeful cands still in the running *)
     * (list cand)            (* elected candidates *)
     * (cand -> nat)          (* tally *)
     -> Node
  | winners:                  (** final state **)
    list cand -> Node.        (* election winners *)

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


Inductive Pf (b: list ballot) (q: nat) (s: nat) : Node -> Type := 
  ax :  forall u r h e t,                      (** start counting **)
  u = b ->                                      (* if the list of ballots contaeqe all ballots *)
  r = s ->
  e = nbdy ->
  PD h  ->
  t = nty ->
  Pf b q s (state (u, r , h, e, t))              (* we start counting with null tally, assignment and elected cands *)
| el : forall u r h e t hn tc,                 (** eliminate **) (* TODO: TRANSFER VOTE *)
  Pf b q s (state (u, r, h, e, t)) ->
  length h > r ->                                (* more hopefuls than seats *)
  (forall i : cand , (In i h) -> t i < q) ->      (* no candidate has required quota *)
  (forall i : cand , (In i h) -> t tc <= t i) ->  (* cand has the lowest tally *)
  eqe tc hn h ->
  In tc h ->
  Pf b q s (state (u, r, hn, e, t))
(*| vt : forall u r h e t tn,
  Pf b q s (state (u, r, h, e, t)) ->
  (forall i : cand, (In i h) -> t i = length ()) ->
  Pf b q s (state (u, r, h, e, tn)) *)
| ec : forall u r h e t hn en tc,                (** elect **)
  Pf b q s (state (u, r, h, e, t)) ->
  t tc >= q ->
  eqe tc hn h ->
  eqe tc e hn ->
  Pf b q s (state (u, r, hn, en, t))
| ew : forall u r h e t w,                      (** elected win **)
  Pf b q s (state (u, r, h, e, t)) ->           (* if at any time *)
  length h <= r ->                               (* we have as many elected candidates as setas *) 
  w = e ++ h ->                                      (* and the winners are precisely the electeds *)
  Pf b q s (winners w).                         (* they are declared the winners *)

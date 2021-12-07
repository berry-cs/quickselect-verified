From Coq Require Import Arith.Arith.
From Coq Require Import Nat.
From Coq Require Import Lists.List.
Import ListNotations.
Require Import Coq.Program.Wf.
Require Import Lia.


Definition gtb (n m : nat) : bool :=
  ltb m n.

Ltac blia :=
  try match goal with
  | |- true = _ => symmetry
  | |- false = _ => symmetry
    end;
  unfold gtb in *;
  try rewrite Nat.ltb_lt in *;
  try rewrite Nat.ltb_nlt in *;
  try rewrite Nat.eqb_eq in *;
  try rewrite Nat.eqb_neq in *;
  try rewrite Nat.leb_le in *;
  try rewrite Nat.leb_nle in *;
  try lia; auto.

Fixpoint count (f: nat -> nat -> bool) (v : nat) (l : list nat) : nat :=
  match l with
  | nil => 0
  | h :: t => if (f h v)
              then S (count f v t)
              else (count f v t)
  end.

Example count_1: (count Nat.ltb 3 [1;2;2;3;3;3]) = 3.
Proof. reflexivity. Qed.
Example count_2: count Nat.eqb 3 [1;2;2;3;3;3] = 3.
Proof. reflexivity. Qed.
Example count_3: count gtb 3 [1;2;2;3;3;3] = 0.
Proof. reflexivity. Qed.


(*
Fixpoint partition (n:nat) (l:list nat) (smaller:list nat) (equal:list nat) (larger:list nat)
  : (list nat * list nat * list nat) :=
  match l with
  | nil => (smaller, equal, larger)
  | h :: t => if (h <? n)
              then partition n t (h::smaller) equal larger
              else if (h =? n)
                   then partition n t smaller (h::equal) larger
                   else partition n t smaller equal larger
  end.
*)

Fixpoint partitionSmaller (n : nat) (l : list nat) : (list nat) :=
 match l with 
  | nil => []
  | h :: t => match (partitionSmaller n t) with
              |smaller 
                => if h <? n
                   then (h :: smaller)
                   else partitionSmaller n t
              end
  end.

Example test_partitionS_1: partitionSmaller 3 [1;2;4;5] = [1;2].
Proof. reflexivity. Qed.

Example test_partitionS_2: partitionSmaller 10 [1;2;4;5] = [1;2;4;5].
Proof. reflexivity. Qed.

Example test_partitionS_3: partitionSmaller 1 [7;2;1;4;5] = ([]).
Proof. reflexivity. Qed.



Fixpoint partitionLarger (n : nat) (l : list nat) : (list nat) :=
 match l with 
  | nil => []
  | h :: t => match (partitionLarger n t) with
              |Larger
                => if gtb h  n
                   then (h :: Larger)
                   else partitionLarger n t
              end
  end.

Example test_partitionL_1: partitionLarger 3 [1;2;4;5] = [4;5].
Proof. reflexivity. Qed.

Example test_partitionL_2: partitionLarger 10 [1;2;4;5] = [].
Proof. reflexivity. Qed.

Example test_partitionL_3: partitionLarger 1 [7;2;1;4;5] = ([7;2;4;5]).
Proof. reflexivity. Qed.


Fixpoint partitionEqual (n : nat) (l : list nat) : (list nat) :=
 match l with 
  | nil => []
  | h :: t => match (partitionEqual n t) with
              |EqualList
                => if  h =? n
                   then (h :: EqualList)
                   else partitionEqual n t
              end
  end.

Example test_partitionE_1: partitionEqual 3 [1;2;3;4;3;5] = [3;3].
Proof. reflexivity. Qed.

Example test_partitionE_2: partitionEqual 10 [1;2;4;5] = [].
Proof. reflexivity. Qed.

Example test_partitionE_3: partitionEqual 1 [7;2;1;4;5] = ([1]).
Proof. reflexivity. Qed.




Lemma part_smaller_count : forall n l, 
  count Nat.ltb n l = length (partitionSmaller n l).
Proof.
  induction l as [ | h t].
  - simpl; auto.
  - simpl.
    destruct (h <? n) eqn:Hlt; simpl; auto.
Qed.

Lemma part_larger_count : forall n l, 
  count gtb n l = length (partitionLarger n l).
Proof.
  induction l as [ | h t].
  - simpl; auto.
  - simpl.
    destruct (gtb h n) eqn:Hlt; simpl; auto.
Qed.

Lemma part_equal_count : forall n l, 
  count Nat.eqb n l = length (partitionEqual n l).
Proof.
  induction l as [ | h t].
  - simpl; auto.
  - simpl.
    destruct (h =? n) eqn:Hlt; simpl; auto.
Qed.

Lemma part_larger_length : forall n l,
    length (partitionLarger n l) <= length l.
    (*the length of partitionLarger will always be less than 
      or equal to the length of the list*)
Proof.
  (*induction on the list, simp and auto take care of the first case*)
  induction l as [ | h t IHl]; simpl; auto.
  (*if the head of the list is greater than n,
    then cons H onto partition Larger and recursive call
    else partitinLarger is less than or equal to the length of the tail + 1*)
  (*we destruct gtb, which gives us (gtb h n) = true, simpl auto takes care of the case*)
  destruct (gtb h n) eqn:Hlt; simpl; auto.
  (*The length of partitinLarger + 1 is less than or equal to the length of the tail + 1 *)
  Search (S _ <= S _).
  (*le_n_s = n <= m -> s n <= s m*)
  (*basically getting rid of the S on both sides, letting us use IHl*)
  apply le_n_S.
  auto.
Qed.

Lemma part_smaller_length : forall n l,
    length (partitionSmaller n l) <= length l.
Proof.
  induction l as [ | h t IHl]; simpl; auto.
  destruct (ltb h n) eqn:Hlt; simpl; auto.
  apply le_n_S; auto.
Qed.

Lemma part_equal_length : forall n l,
    length (partitionEqual n l) <= length l.
Proof.
  induction l as [ | h t IHl]; simpl; auto.
  destruct (eqb h n) eqn:Hlt; simpl; auto.
  apply le_n_S; auto.
Qed.



(* q_s finds the nth largest thing in the given list *)

(* We had to give it an additional input "steps"  
so that the function could run recursively; without steps it was unable to tell
whether or not the function would always terminate. *)
Fixpoint q_s (steps:nat) (n : nat) (l : list nat) : option nat :=
  (* actual recursion happens until steps runs out to 0*)
  match steps with
   | 0 => None
   | S steps' =>
      match l with

      (*if list is empty we return none (used option as return type) *)
      | nil => None
      
      (* if list is nonempty run 3 partition funcs on t with h as pivot, creating 3 lists 
       to use *)   
      | h :: t => let  larger := partitionLarger h t in
                  let  smaller := partitionSmaller h t in
                  let  equal := partitionEqual h t in
      (* if n < length of larger, we know ans must be in partLarger *)
      if n <=? length larger then
         q_s steps' n larger else
      (* if n > sum of length large and equal, we know ans is partSmaller *)
         if (length larger + length equal + 1) <? n then
       (*must subtract from n because we are now starting q_s over in smaller; don't want 
         orignial nth largest from this list*)
         q_s steps' (n - (length larger + length equal + 1)) smaller else
       (*finally have that ans is in partEqual and return it  *)
         Some h
      end
  end.

(* We defined this function to use q_s on the given n and l and it automatically tells 
q_s that (length l) steps are required; this works because the number of steps necessary
to find ans is always gonna be less than the length of orig list, but probably not equal.
*)
Definition quick_select (n : nat) (l : list nat) : option nat :=
  q_s (length l) n l.

Compute (quick_select 1 [1;4;3;5]).
Compute  quick_select 2 [4;5;2;1].

Example quick_select_1: quick_select 1 [1;2;4;5] = Some 5.
Proof. reflexivity. Qed.
Example quick_select_2: quick_select 2 [1;2;4;5] = Some 4.
Proof. reflexivity. Qed.
Example quick_select_3: quick_select 2 [4;5;2;1] = Some 4.
Proof. reflexivity. Qed.
Example quick_select_4: quick_select 4 [50;60;4;9;21;35] = Some 21.
Proof. reflexivity. Qed.
Example quick_select_5: quick_select 2 [] = None.
Proof. reflexivity. Qed.
Example quick_select_6: quick_select 5 [1;2;4;5] = None.
Proof. reflexivity. Qed.
Example quick_select_7: quick_select 0 [1;2;4;5] = None.
Proof. reflexivity. Qed.




(* ********************************************************************* *)
(* ********************************************************************* *)
(* ********************************************************************* *)
(* ********************************************************************* *)
(* ********************************************************************* *)


(*
  Hints: after induction, simpl, and handling the basic cases,
         destruct (gtb a h). unfold gtb so that it shows as <? 
         and use Nat.ltb_lt  (to rewrite) *)
Lemma In_part_larger : forall lst h x, In x (partitionLarger h lst) -> h < x.
      (* if X is within the partitionLarger, then the head of the list is < x *)
Proof.
  intros lst h x H.
(*call induction on the list*)
  induction lst as [ | head t IHl].
  (*first case is proving that x is within an empty list, therefore nothing is larger than h*)
  (*simpl in H, gives us that H is false, then destruct and it takes care of that case*)
  -simpl in H. destruct H.
(* destruct gives us Heqn (gtb head h) = true*)
  -simpl in H. destruct (gtb head h) eqn:Heqn; auto.
  -- blia. (* unfold gtb in Heqn. apply Nat.ltb_lt in Heqn. *)
     (*destruct H to focus on each part of the or *)
     simpl in H. destruct H.
     (*H is head = X, Heqn is h < head, so replace x with head to get h < x in Heqn*)
     replace x with head; auto.
     (*auto takes care of the last case*)
     auto.
Qed.

(* Hints: after induction, simpl, and handling the basic cases,
         destruct (a <? h), and use Nat.ltb_lt (to rewrite) *)
Lemma In_part_smaller : forall lst h x, In x (partitionSmaller h lst) -> x < h.
Proof.
  intros lst h x H.
  induction lst as [ | head t IHl].
  -simpl in H. destruct H.
  -simpl in H. destruct (ltb head h) eqn:Heqn; auto.
   + unfold gtb in Heqn. apply Nat.ltb_lt in Heqn.
     simpl in H. destruct H.
     replace x with head; auto.
     auto.
Qed.

(* Hints: remember to unfold gtb to get it showing as <? after simpl'ing
          destruct (p <? h) and rewrite with Nat.ltb_lt *)
Lemma In_part_larger_In_list : 
             forall v p l, p < v -> In v (partitionLarger p l) -> In v l.
Proof.
  intros v p l H1 H2.
  induction l as [ | h t IHl].
  - simpl in H2. destruct H2.
  - simpl. simpl in H2. unfold gtb in H2. destruct (p <? h) eqn:Heqn; auto.
   + simpl in H2. destruct H2.
    * left; auto.
    * right; auto.
Qed. 


Lemma In_part_smaller_In_list : 
             forall v p l, v < p -> In v (partitionSmaller p l) -> In v l.
Proof.
  intros v p l H1 H2.
  induction l as [ | h t IHl].
  - simpl in H2. destruct H2.
  - simpl. simpl in H2. destruct (h <? p) eqn:Heqn; auto.
   + simpl in H2. destruct H2.
    * left; auto.
    * right; auto.
Qed. 


(* Hints:
   - general idea: induction steps, then destruct lst.
   - use discriminate to eliminate silly cases.
   - destruct things like (n <=? length (partitionLarger h lst')) that are 
     blocking simplification
   - use In_part_larger_In_list, In_part_larger, etc.
*)
Lemma In_qs : forall steps n lst v, q_s steps n lst = Some v -> In v lst.
Proof.
  (*the result of q_S (Some V) is in the given list*)
  intros steps .
  induction steps as [ | steps' IHs ]; intros n lst v H.
    (*we simplify H and see that Some V is nothing, so we descriminate the case*)
  - simpl in H. discriminate H.
    (*we destruct the list to empty and h :: t*)
  - destruct lst as [ | h t ].
    (*we start with the empty case, since the list is empty v cant be in the list,
      so we discriminate*)
   + simpl in H. discriminate H.
    (*simplified H, and destructed the if conditions into 
      Heqn: (n <=? length (partitionLarger h t)) = true. Blia finishes it off*) 
   + simpl.  simpl in H. destruct (n <=? length (partitionLarger h t)) eqn:Heqn; blia.
    (*sub case where V is in partitionLarger*)
    (*we focus the right side, and apply a helper lemma (In_part_larger_In_list), 
      then blia finishes it off*)
    * apply IHs in H. right. apply In_part_larger_In_list with h; blia.
        (*we apply helper Lemma (In_part_larger) on the tail then auto*)
      -- apply In_part_larger with t; auto.
    (* Case where v is in the smaller list *)
    (* we destruct the if conditions into Heqn2, then apply blia*)
    * destruct (length (partitionLarger h t) + length (partitionEqual h t) + 1 <? n) eqn:Heqn2; blia.
        (*focus on the right side, then apply In_part_smaller_In_list, then blia*)
      -- apply IHs in H. right. apply In_part_smaller_In_list with h; blia.
        (*we apply in_part_smaller then auto*)
        ++ apply In_part_smaller with t; auto.
      (*focus on the left side, inject H, then auto*)
      -- left. injection H. auto.
Qed.



(* Hints:
   - induction l. unfold gtb.
   - lots of rewriting  Nat.ltb_lt, Nat.ltb_nlt, Nat.eqb_neq, Nat.eqb_eq
     (use symmetry if necessary to flip left/right of the = )
   - use:  lia  to handle arithmetic reasoning automatically
*)
Lemma counts_add_up :
  forall p l, count gtb p l + count Nat.eqb p l + count Nat.ltb p l = length l.
Proof.
  intros p l.
  induction l as [ | h t ]; blia.
  - simpl. destruct (p <? h) eqn:Heqn1; blia.
   + replace (h =? p) with false; blia; replace (h <? p) with false; blia.
   + destruct (h =? p) eqn:Heqn.
    * replace (h <? p) with false; blia.
    * replace (h <? p) with true; blia.
Qed.



(* Hints:
   - induction on lst. similar hints as the previous one.
*)
Lemma count_part_larger_lt :
  forall lst p v, p < v -> count gtb v lst = count gtb v (partitionLarger p lst).
Proof.
  intros lst p v H.
  induction lst as [ | h t IHl ]; auto.
  - simpl. unfold gtb. destruct (v <? h) eqn:Heqn1.
  + simpl. destruct (p <? h)eqn:Heqn2. blia.
     simpl.
    replace (v <? h) with true; blia.
   blia.

  + destruct (p <? h) eqn:Heqn2; blia.
    simpl. replace (v <? h) with false; blia. 
Qed.
 


(* Hints:
   - induction on l. use simpl; auto  a lot. also lia.
*)
Lemma count_part_smaller_lt :
  forall v p l, v < p -> count Nat.ltb v (partitionSmaller p l) = count Nat.ltb v l.
Proof.
  intros v p l H.
  induction l as [ | h t IHl ]; auto.
  - simpl. destruct (h <? p) eqn:Heqn1. auto.
   + simpl. destruct (h <? v) eqn:Heqn2; auto.
   + simpl. destruct (h <? v) eqn:Heqn2; blia.
    (* * simpl. apply Nat.ltb_nlt in Heqn1. apply Nat.ltb_lt in Heqn2. lia.
       * apply IHl. *)
Qed.


(* Hints:
   - induction on l, several destructs with ...; simpl; auto  after them makes it short.
   - rewrite with Nat.ltb_nlt, Nat.eqb_eq 
*)
Lemma count_part_smaller_eq :
  forall v p l, v < p -> count Nat.eqb v (partitionSmaller p l) = count Nat.eqb v l.
Proof.
  induction l as [ | h t ]; auto.
  intros Hlt.
  simpl.
  destruct (h <? p) eqn:Heq1; simpl; destruct (h =? v) eqn:Heq2; blia; simpl.
Qed.

Lemma part_smaller_chunk :
  forall v h,
    v < h -> forall l,
      length (partitionLarger v (partitionSmaller h l)) +
      length (partitionLarger h l) + length (partitionEqual h l) =
      length (partitionLarger v l).
Proof.
  intros.
  repeat rewrite <- part_larger_count.
  rewrite <- part_equal_count.
  assert (H1:=counts_add_up h l).
  assert (H2:=counts_add_up v (partitionSmaller h l)).
  assert (H3:=counts_add_up v l).
  rewrite <- part_smaller_count in H2.
  rewrite <- H3 in H1.
  rewrite <- H2 in H1.

  replace (count Nat.eqb v l) with (count Nat.eqb v (partitionSmaller h l)) in H1.
  replace (count Nat.ltb v l) with (count Nat.ltb v (partitionSmaller h l)) in H1.
  lia.

  apply count_part_smaller_lt; auto.
  apply count_part_smaller_eq; auto.
Qed.



Lemma qs_theorem_gtb : forall (steps n v: nat) (l : list nat),
    length l <= steps ->
    q_s steps n l = Some v -> 
    (count gtb v l) < n.
Proof.
  induction steps as [ | steps' IHsteps]; intros n v l Hlen Hqs.
  - simpl in Hqs.
    discriminate.

  - destruct l as [ | h l'].
    -- simpl in *; discriminate.
    -- simpl in Hqs.
       destruct (n <=? length (partitionLarger h l')) eqn:Heq1.
       --- Search (_ <=? _ = true).
           rewrite Nat.leb_le in Heq1.
           assert (h < v).
           { apply In_part_larger with l'.
             apply In_qs with steps' n; auto. }
           simpl; replace (gtb h v) with false. 2: { blia. }
           
           assert (Hcount := Hqs).
           apply IHsteps in Hcount.

           ---- Search (_ < _ -> _ <= _ -> _ < _).
                rewrite count_part_larger_lt with l' h v; auto.

           ---- simpl in Hlen.
                assert (length l' <= steps'); try lia.
                apply Nat.le_trans with (length l'); auto.
                apply part_larger_length; auto.

       --- rewrite Nat.leb_nle in Heq1.
           destruct (length (partitionLarger h l') + length (partitionEqual h l') + 1 <? n) eqn:Heq2.

           2: {
             injection Hqs; intros.
             replace h with v in *; simpl.
             replace (gtb v v) with false.
             rewrite Nat.ltb_nlt in Heq2.
             rewrite part_larger_count.
             lia.
             unfold gtb. symmetry. apply Nat.ltb_irrefl.
           }

           apply Nat.ltb_lt in Heq2.
           assert (length (partitionLarger h l') < n); try lia.
           assert (Hcount := Hqs).
           apply IHsteps in Hqs.
           simpl.

           apply In_qs in Hcount.
           apply In_part_smaller in Hcount.
           unfold gtb at 1.
           apply Nat.ltb_lt in Hcount; rewrite Hcount.
           rewrite part_larger_count.
           rewrite Nat.ltb_lt in Hcount.
           rewrite part_larger_count in Hqs.

           replace (length (partitionLarger v l')) with
               (length (partitionLarger v (partitionSmaller h l'))
                + length (partitionLarger h l') + length (partitionEqual h l')).
           lia.

           apply part_smaller_chunk; auto.

           simpl in Hlen.
           apply Nat.le_trans with (length l'); try lia.
           apply part_smaller_length.
Qed.



Theorem quickselect_theorem : forall (n v: nat) (l : list nat),
  quick_select n l = Some v -> 
  (count gtb v l) < n /\ (count Nat.eqb v l) <= (length l) /\ 
  (count Nat.ltb v l) <= ((length l)-n).
Proof.
  intros n v l H.
  unfold quick_select in H.
  split.
  - apply qs_theorem_gtb with (length l); auto.
  - split.
    --
    --
Qed.

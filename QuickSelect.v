From Coq Require Import Arith.Arith.
From Coq Require Import Nat.
From Coq Require Import Lists.List.
Import ListNotations.
Require Import Coq.Program.Wf.
Require Import Lia.

Definition gtb (n m : nat) : bool :=
  ltb m n.


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
Proof.
  induction l as [ | h t IHl]; simpl; auto.
  destruct (gtb h n) eqn:Hlt; simpl; auto.
  Search (S _ <= S _).
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


Fixpoint q_s (steps:nat) (n : nat) (l : list nat) : option nat :=
  match steps with
   | 0 => None
   | S steps' =>
      match l with
      | nil => None
      | h :: t => let  larger := partitionLarger h t in
                  let  smaller := partitionSmaller h t in
                  let  equal := partitionEqual h t in
      if n <=? length larger then
         q_s steps' n larger else
         if (length larger + length equal + 1) <? n then
         q_s steps' (n - (length larger + length equal + 1)) smaller else
         Some h
      end
  end.

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
Proof.
Admitted.


(* Hints: after induction, simpl, and handling the basic cases,
         destruct (a <? h), and use Nat.ltb_lt (to rewrite) *)
Lemma In_part_smaller : forall lst h x, In x (partitionSmaller h lst) -> x < h.
Proof.
Admitted.


(* Hints: remember to unfold gtb to get it showing as <? after simpl'ing
          destruct (p <? h) and rewrite with Nat.ltb_lt *)
Lemma In_part_larger_In_list : 
             forall v p l, p < v -> In v (partitionLarger p l) -> In v l.
Proof.
Admitted.


Lemma In_part_smaller_In_list : 
             forall v p l, v < p -> In v (partitionSmaller p l) -> In v l.
Proof.
Admitted.


(* Hints:
   - general idea: induction steps, then destruct lst.
   - use discriminate to eliminate silly cases.
   - destruct things like (n <=? length (partitionLarger h lst')) that are 
     blocking simplification
   - use In_part_larger_In_list, In_part_larger, etc.
*)
Lemma In_qs : forall steps n lst v, q_s steps n lst = Some v -> In v lst.             
Proof.
Admitted.


(* Hints:
   - induction l. unfold gtb.
   - lots of rewriting  Nat.ltb_lt, Nat.ltb_nlt, Nat.eqb_neq, Nat.eqb_eq
     (use symmetry if necessary to flip left/right of the = )
   - use:  lia  to handle arithmetic reasoning automatically
*)
Lemma counts_add_up :
  forall p l, count gtb p l + count Nat.eqb p l + count Nat.ltb p l = length l.
Proof.
Admitted.


(* Hints:
   - induction on lst. similar hints as the previous one.
*)
Lemma count_part_larger_lt :
  forall lst p v, p < v -> count gtb v lst = count gtb v (partitionLarger p lst).
Proof.
Admitted.


(* Hints:
   - induction on l. use simpl; auto  a lot. also lia.
*)
Lemma count_part_smaller_lt :
  forall v p l, v < p -> count Nat.ltb v (partitionSmaller p l) = count Nat.ltb v l.
Proof.
Admitted.


(* Hints:
   - induction on l, several destructs with ...; simpl; auto  after them makes it short.
   - rewrite with Nat.ltb_nlt, Nat.eqb_eq 
*)
Lemma count_part_smaller_eq :
  forall v p l, v < p -> count Nat.eqb v (partitionSmaller p l) = count Nat.eqb v l.
Proof.
Admitted.


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
           simpl; replace (gtb h v) with false.
           2: { unfold gtb. symmetry; apply Nat.ltb_nlt. lia. }
           assert (Hcount := Hqs).
           apply IHsteps in Hcount; try lia.

           ---- Search (_ < _ -> _ <= _ -> _ < _).
                apply Nat.le_lt_trans with (count gtb v (partitionLarger h l')); auto.
                (*assert (n > 0); try lia.*)
                (*assert (length (partitionLarger h l') > 0); try lia.*)
                rewrite <- count_part_larger_lt; auto.

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
             unfold gtb; symmetry; apply Nat.ltb_irrefl.
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




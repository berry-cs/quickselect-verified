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



Lemma quickselect_theorem_gtb : forall (steps n v: nat) (l : list nat),
    length l <= steps ->
    quick_select n l = Some v -> 
    (count gtb v l) < n.
Proof.
  induction steps as [ | steps' IHsteps]; unfold quick_select; intros n v l Hlen Hqs.
  - assert (length l = 0).
    { lia. }
    rewrite H in Hqs; simpl in Hqs.
    discriminate.

  - rewrite part_larger_count.
    destruct l as [ | h l'].
    -- simpl in *; discriminate.
    -- simpl in Hqs.
       destruct (n <=? length (partitionLarger h l')) eqn:Heq1.
       --- Search (_ <=? _ = true).
           rewrite Nat.leb_le in Heq1.
           simpl.
           replace (gtb h v) with false.
           ---- rewrite <- part_larger_count.
                apply IHsteps.
                simpl in Hlen; lia.
                unfold quick_select.





Theorem quickselect_theorem : forall (n v: nat) (l : list nat),
  quick_select n l = Some v -> 
  (count gtb v l) <= (n-1) /\ (count Nat.eqb v l) <= (length l) /\ 
  (count Nat.ltb v l) <= ((length l)-n).
Proof.
  intros n v l H.
  split.
  - induction l as [ | h t IHl].
   + discriminate H.
   + simpl. destruct (gtb h v) eqn:Heqn.
    * Search (_ <= _). apply le_Sn_le.






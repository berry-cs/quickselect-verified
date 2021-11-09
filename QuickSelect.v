From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
Require Export Coq.Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Lists.List.
Import ListNotations.


Fixpoint partition (n : nat) (l : list nat) : (list nat * list nat) :=
  match l with 
  | nil => ([],[])
  | h :: t => let P := (partition n t) in
                if h <? n
               then (h :: (fst P), snd P)
               else (fst P, h :: (snd P))
  end.

Example test_partition_1: partition 3 [1;2;4;5] = ([1;2],[4;5]).
Proof. reflexivity. Qed.

Example test_partition_2: partition 10 [1;2;4;5] = ([1;2;4;5],[]).
Proof. reflexivity. Qed.

Example test_partition_3: partition 1 [7;2;4;5] = ([],[7;2;4;5]).
Proof. reflexivity. Qed.

Require Import Coq.Program.Wf.
Require Import Lia.

Lemma partition_length_fst : forall (n : nat) (l : list nat),
  (length (fst (partition n l))) <= (length l).
Proof.
  intros n l.
  induction l as [ | h t IHl].
  -simpl. reflexivity.
  -simpl. destruct (h <? n) eqn:Heqn; simpl; lia. 
Qed.

Lemma partition_length_snd : forall (n : nat) (l : list nat),
  (length (snd (partition n l))) <= (length l).
Proof.
  intros n l.
  induction l as [ | h t IHl].
  -simpl. reflexivity.
  -simpl. destruct (h <? n) eqn:Heqn; simpl; lia. 
Qed.

Program Fixpoint quick_select (n : nat) (l : list nat) {measure (length l)} : option nat :=
  match l with
  | nil => None 
  | h :: t => match (partition h t) with
              | ( smaller, larger ) =>
               if n =? 1+(length larger)
               then Some h
               else if n <=? (length larger)
                    then (quick_select n  larger)
                    else (quick_select ((n-(length larger))-1)  smaller)
               end
  end.
Next Obligation.
simpl.
assert (length (snd (partition h t)) <= (length t)).
- apply partition_length_snd.
- rewrite <- Heq_anonymous in H. simpl in H. lia.
Qed.

Next Obligation.
simpl.
assert (length (fst (partition h t)) <= (length t)).
- apply partition_length_fst.
- rewrite <- Heq_anonymous in H. simpl in H. lia.
Qed.


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





(****************Homework 3************Due: 3pm Oct. 3rd*****************************************************)
(*****To prove some of the following theorems, you may need to first prove some lemmas.***************************)
(*****You are welcome to use whatever is proved in the class in Basics.v and Lists.v *****************************)
(*****For this homework, automatic tactics of Coq (auto, tauto, trivial, intuition, omega, etc.) are not allowed.*)

(***********************************************************************)
(***** Submit solutions in a single coq file via email to the TAs ******)
(***********************************************************************)








(******************************* question 1*******************************************************8 points*)
(** Prove [andb_true_elim2], marking cases (and subcases) when
    you use [destruct]. *)

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
intros.
destruct c.
(* Case c = true *)
reflexivity.
(* Case c = false *)
rewrite <- H.
destruct b.
(* Case b = true *)
reflexivity.
(* Case b = false *)
reflexivity.
Qed.

(******************************* question 2*******************************************************16 points*)

(*a*)
Theorem plus_assoc : forall n m p : nat,
n + (m + p) = (n + m) + p.
Proof.
intros.
induction n.
reflexivity.
simpl.
rewrite -> IHn.
reflexivity.
Qed.

(*b*)
Theorem plus_distr : forall n m: nat, S (n + m) = n + (S m).
Proof.
intros.
induction n.
induction m.
simpl.
reflexivity.
rewrite <- IHm.
simpl.
reflexivity.
simpl.
rewrite <- IHn.
reflexivity.
Qed.

(*c*)
Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
intros.
induction n.
induction m.
reflexivity.
simpl.
rewrite <- IHm.
simpl.
reflexivity.
simpl.
rewrite -> IHn.
apply plus_distr.
Qed.
(** [] *)

(*d*)
(** Translate your solution for [plus_comm] into an informal proof. *)

(** Theorem: Addition is commutative.
             forall n m : nat, n + m = m + n
 
    Proof: 
    Induct on n and m.

      n = 0, m = 0
      0 + 0 = 0 + 0
      0 = 0
      True

      n = 0
      IH: 0 + m = m + 0
      P(k+1) => 1 + m = 1 + (m+0)
         By IH: 1 + m = 1 + (0+m)
                1 + m = 1 + m
                True

      IH: n + m = m + n
      P(k+1) => (1+n) + m = m + (1+n)
                1 + (n + m) = m + (1+n)
                By IH: 1 + (m + n) = m + (1+n)
                By distr: 1 + m + n = 1 + m + n
                True
[]
*)


(******************************* question 3*******************************************************8 points*)

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n, double n = n + n .
Proof. 
intros. 
induction n.
reflexivity.
simpl.
rewrite -> IHn.
rewrite <- plus_distr.
reflexivity.
Qed.


(******************************* question 4*******************************************************8 points*)

(** Use [assert] to help prove this theorem.  You shouldn't need to use induction. *)

Theorem plus_swap : forall n m p : nat, 
  n + (m + p) = m + (n + p).
Proof.
intros.
rewrite -> plus_assoc.
rewrite -> plus_assoc.
assert (H1: n + m = m + n).
apply plus_comm.
rewrite <- H1.
reflexivity.
Qed.

(******************************* question 5*******************************************************10 points*)

Lemma mult_zero : forall n : nat, n * 0 = 0.
Proof.
intros.
induction n.
reflexivity.
simpl.
rewrite -> IHn.
reflexivity.
Qed.

Lemma mult_iden : forall n m : nat, n + n * m = n * S m.
Proof.
intros.
induction n.
induction m.
reflexivity.
reflexivity.
simpl.
rewrite <- IHn.
rewrite -> plus_assoc.
rewrite -> plus_assoc.
assert (H: n + m = m + n).
rewrite -> plus_comm.
reflexivity.
rewrite -> H.
reflexivity.
Qed.


Theorem mult_comm : forall m n : nat,
 m * n = n * m.
Proof.
intros.
induction m.
simpl.
rewrite -> mult_zero.
reflexivity.
induction n.
simpl.
rewrite -> mult_zero.
reflexivity.
simpl.
rewrite -> IHm.
simpl.
rewrite -> plus_swap.
rewrite -> mult_iden.
reflexivity.
Qed.


(******************************* question 6*******************************************************10 points*)

Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
intros.
induction n.
induction m.
simpl.
reflexivity.
simpl.
reflexivity.
simpl.
rewrite -> IHn.
rewrite -> plus_assoc.
reflexivity.
Qed.

(***** Some definitions/notations for lists, as we saw in class *****)

Inductive natlist : Type :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.

Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).

Fixpoint app (l1 l2 : natlist) : natlist := 
  match l1 with
  | nil    => l2
  | h :: t => h :: (app t l2)
  end.

Notation "x ++ y" := (app x y) 
                     (right associativity, at level 60).

Fixpoint snoc (l:natlist) (v:nat) : natlist := 
  match l with
  | nil    => [v]
  | h :: t => h :: (snoc t v)
  end.

Fixpoint rev (l:natlist) : natlist := 
  match l with
  | nil    => nil
  | h :: t => snoc (rev t) h
  end.







(******************************* question 7*******************************************************12 points*)

(*a*) (* 2 points *)
Theorem app_nil_end : forall l : natlist, 
  l ++ [] = l.   
Proof.
intros.
induction l.
simpl.
reflexivity.
simpl.
rewrite -> IHl.
reflexivity.
Qed.

Lemma snoc_rev : forall (l:natlist) (n:nat), rev(snoc l n) = n::rev(l).
Proof.
intros.
induction l.
simpl.
reflexivity.
simpl.
rewrite -> IHl.
simpl.
reflexivity.
Qed.

(*b*) (* 10 points *)
Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
intros.
induction l.
simpl.
reflexivity.
simpl.
rewrite -> snoc_rev.
rewrite -> IHl.
reflexivity.
Qed.




(******************************* question 8*******************************************************16 points*)

(*a*) (* 4 points *)
Theorem snoc_append : forall (l:natlist) (n:nat),
  snoc l n = l ++ [n].
Proof.
intros.
induction l.
reflexivity.
simpl.
rewrite <- IHl.
reflexivity.
Qed.

Lemma distr_snoc : forall (l1 l2 : natlist) (n:nat), snoc (l1 ++ l2) n = l1 ++ snoc l2 n.
intros.
induction l1.
induction l2.
simpl.
reflexivity.
simpl.
reflexivity.
simpl.
rewrite IHl1.
reflexivity.
Qed.


(*b*) (* 12 points *)
Theorem distr_rev : forall l1 l2 : natlist,
  rev (l1 ++ l2) = (rev l2) ++ (rev l1).
Proof.
intros.
induction l1.
induction l2.
simpl.
reflexivity.
simpl.
rewrite app_nil_end.
reflexivity.
simpl.
rewrite -> IHl1.
rewrite -> distr_snoc.
reflexivity.
Qed.


(***** Some definitions on bags, as we saw in class *****)

Definition bag := natlist.

Fixpoint ble_nat (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => ble_nat n' m'
      end
  end.

Require Import Arith.

Fixpoint count (v:nat) (s:bag) : nat := 
  match s with
    nil => 0
  | h :: t => if (beq_nat h v) then S (count v t)
                               else count v t
  end.


Fixpoint remove_one (v:nat) (s:bag) : bag :=
  match s with
    nil => nil
  | h::t => if (beq_nat v h)
             then t
             else h::(remove_one v t)
  end.






(******************************* question 9*******************************************************12 points*)

(*a*) (* 2 points *)
Theorem count_member_nonzero : forall (s : bag),
  ble_nat 1 (count 1 (1 :: s)) = true.
Proof.
intros.
induction s.
simpl.
reflexivity.
simpl.
reflexivity.
Qed.




(** The following lemma about [ble_nat] might help you in the next proof. *)

Theorem ble_n_Sn : forall n,
  ble_nat n (S n) = true.
Proof.
  intros n. induction n as [| n'].
    simpl.  reflexivity.
    simpl.  rewrite IHn'.  reflexivity.  Qed.

(*b*) (* 10 points *)
Theorem remove_decreases_count: forall (s : bag),
  ble_nat (count 0 (remove_one 0 s)) (count 0 s) = true.
Proof.
intros.
induction s.
simpl.
reflexivity.
destruct n.
simpl.
rewrite -> ble_n_Sn.
reflexivity.
simpl.
rewrite IHs.
reflexivity.
Qed.



(******************************* BONUS QUESTION*******************************************************10 points*)

Theorem rev_inj : forall (l1 l2 : natlist), rev l1 = rev l2 -> l1 = l2.
Proof.
intros.
rewrite <- (rev_involutive l2).
rewrite <- (rev_involutive l1).
rewrite <- H.
reflexivity.
Qed.
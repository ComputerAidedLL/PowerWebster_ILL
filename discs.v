(*** *********************** ***)
(*** TOWERS OF HANOI - DISCS ***)
(*** *********************** ***)

(* James Power * James.Power@May.ie * http://www.cs.may.ie/~jpower/ *)
(* Dept. of Computer Science, NUI Maynooth, Co. Kildare, Ireland.   *)

(* This file is part of the Towers of Hanoi in ILL example
 * In it, we define the discs and the "smaller" relation
 * as well as some lemmas relating to quantification over disc-lists
 *)

Require PolyList.
Require TheoryList.
Require PolyListSyntax.

(*************)
(*** DISCS ***)
(*************)

Parameter Disc : Set.

Parameter smaller : Disc -> Disc -> Prop.

Hypothesis smallTrans : 
  (x,y,z:Disc) (smaller x y) -> (smaller y z) -> (smaller x z).

(* Can we transfer a disc onto a pole? *)
Definition canTxfrTo : Disc -> (list Disc) -> Prop :=
  [d:Disc][ds:(list Disc)] 
  (AllS ([d':Disc](smaller d d')) ds).

(* Can we move a disc-list onto a pole? *)
Definition canMoveTo : (list Disc) -> (list Disc) -> Prop :=
  [d1,d2:(list Disc)] 
  (AllS ([d':Disc](canTxfrTo d' d2)) d1).

(* When is a list of discs in order? *)
Inductive ordered : (list Disc) -> Prop :=
  ord_nil : (ordered Empty)
| ord_cons : (d:Disc)(ds:(list Disc))
             (canTxfrTo d ds) -> (ordered ds) -> (ordered (cons d ds)).


(* *************************** *)
(* Quantifying over disc-lists *)
(* *************************** *)

(* Working with reverse induction and AllS... *)
Lemma OneCat :
  (A:Set) (P:A->Prop) (a:A)(l:(list A))
  (AllS P (l^`a)) -> (P a).
Proof.
Induction l; Simpl.
Intros AS; Inversion AS; Assumption.
Intros a0 l2 IH AS; Inversion AS; Apply IH; Assumption.
Qed.

Lemma AllCat :
  (A:Set) (P:A->Prop) (l1,l2:(list A))
  (AllS P (l1^l2)) -> (AllS P l1).
Proof.
Induction l1.
Intros; Apply allS_nil.
Intros a l IH l2 AS. Simpl in AS. Inversion AS.
Apply allS_cons; [ Assumption | Apply (IH l2); Assumption].
Qed.

Lemma AllCat2 :
  (A:Set) (P:A->Prop) (l1,l2:(list A))
  (AllS P (l1^l2)) -> (AllS P l2).
Proof.
Induction l1.
Simpl; Intros; Assumption.
Intros a l IH l2 AS; Simpl in AS; Inversion AS; Apply (IH l2 H2).
Qed.

Lemma AllCat_Ind :
  (A:Set) (P:A->Prop) (l1,l2:(list A))
  (AllS P l1) -> (AllS P l2) -> (AllS P (l1^l2)).
Proof.
Induction l1.
Simpl; Intros; Assumption.
Intros a l IH l2 AS1 AS2; Inversion AS1; Simpl.
Apply allS_cons; [ Assumption | (Apply (IH l2); Assumption)].
Qed.


Lemma CanMoveEmpty :
  (ds:(list Disc)) (canMoveTo ds Empty).
Proof.
(Induction ds; Unfold canMoveTo).
Apply allS_nil.
Intros; Unfold canTxfrTo; Apply allS_cons; [ Apply allS_nil| Assumption].
Qed.


Lemma CanMoveApp : 
  (ds,d1,d2:(list Disc))
  (canMoveTo ds d1) -> (canMoveTo ds d2) -> (canMoveTo ds (d1^d2)).
Proof.
Induction ds.
Intros; Simpl; Unfold canMoveTo; Apply allS_nil.
Intros a l IH d1 d2 CM1 CM2.
Unfold canMoveTo in CM1; Inversion CM1.
Unfold canMoveTo in CM2; Inversion CM2.
Unfold canMoveTo; Apply allS_cons.
Unfold canTxfrTo; Apply AllCat_Ind; Assumption.
Apply (IH d1 d2); Assumption.
Qed.


Lemma OrdCat :
  (d1,d2:(list Disc)) (ordered (d1^d2)) -> (ordered d1).
Proof.
Induction d1.
Intros; Apply ord_nil.
Intros a l IH d2 ORD.
Simpl in ORD; Inversion ORD; Apply ord_cons.
Unfold canTxfrTo; Unfold canTxfrTo in H1;
  Apply AllCat with l1:=l l2:=d2; Assumption.
Apply (IH d2 H2).
Qed.

Lemma OrdMove :
  (d1,d2:(list Disc)) (ordered (d1^d2)) -> (canMoveTo d1 d2).
Proof.
Induction d1.
Intros; Unfold canMoveTo; Apply allS_nil.
Intros a l IH d2 ORD; Simpl in ORD; Inversion ORD.
Unfold canMoveTo; Unfold canMoveTo in IH; Apply allS_cons.
Unfold canTxfrTo; Unfold canTxfrTo in H1.
Apply AllCat2 with l1:=l l2:=d2; Assumption.
Apply (IH d2); Assumption.
Qed.







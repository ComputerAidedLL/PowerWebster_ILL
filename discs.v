(*** *********************** ***)
(*** TOWERS OF HANOI - DISCS ***)
(*** *********************** ***)

(* James Power * James.Power@May.ie * http://www.cs.may.ie/~jpower/ *)
(* Dept. of Computer Science, NUI Maynooth, Co. Kildare, Ireland.   *)

(* This file is part of the Towers of Hanoi in ILL example
 * In it, we define the discs and the "smaller" relation
 * as well as some lemmas relating to quantification over disc-lists
 *)

From Stdlib Require Import List.
Import ListNotations.
Notation Empty := (@nil _).

(*************)
(*** DISCS ***)
(*************)

Parameter Disc : Set.

Parameter smaller : Disc -> Disc -> Prop.

Axiom smallTrans :
  forall (x y z:Disc), (smaller x y) -> (smaller y z) -> (smaller x z).

(* Can we transfer a disc onto a pole? *)
Definition canTxfrTo : Disc -> list Disc -> Prop :=
  fun (d:Disc) (ds:list Disc) =>
  (Forall (fun d':Disc => smaller d d') ds).

(* Can we move a disc-list onto a pole? *)
Definition canMoveTo : list Disc -> list Disc -> Prop :=
  fun d1 d2:list Disc =>
  (Forall (fun d':Disc => canTxfrTo d' d2) d1).

(* When is a list of discs in order? *)
Inductive ordered : list Disc -> Prop :=
  ord_nil : ordered Empty
| ord_cons : forall (d:Disc)(ds:list Disc),
             canTxfrTo d ds -> ordered ds -> ordered (cons d ds).


Lemma CanMoveEmpty
  (ds:list Disc): canMoveTo ds Empty.
Proof.
induction ds; unfold canMoveTo.
apply Forall_nil.
intros; unfold canTxfrTo; apply Forall_cons; [ apply Forall_nil| assumption].
Qed.


Lemma CanMoveApp
  (ds d1 d2:list Disc):
  canMoveTo ds d1 -> canMoveTo ds d2 -> canMoveTo ds (d1++d2).
Proof.
induction ds as [|a l IH].
intros; simpl; unfold canMoveTo; apply Forall_nil.
intros CM1 CM2.
unfold canMoveTo in CM1; inversion CM1.
unfold canMoveTo in CM2; inversion CM2.
unfold canMoveTo; apply Forall_cons.
unfold canTxfrTo; apply Forall_app; split; assumption.
apply IH; assumption.
Qed.


Lemma OrdCat
  (d1 d2:list Disc): ordered (d1++d2) -> ordered d1.
Proof.
induction d1 as [|a l IH].
intros; apply ord_nil.
intros ORD.
simpl in ORD; inversion ORD; apply ord_cons.
unfold canTxfrTo; unfold canTxfrTo in H1;
  apply Forall_app with (l1:=l) (l2:=d2); assumption.
apply (IH H2).
Qed.

Lemma OrdMove
  (d1 d2:list Disc): ordered (d1++d2) -> canMoveTo d1 d2.
Proof.
induction d1 as [|a l IH].
intros; unfold canMoveTo; apply Forall_nil.
intros ORD; simpl in ORD; inversion ORD.
unfold canMoveTo; unfold canMoveTo in IH; apply Forall_cons.
unfold canTxfrTo; unfold canTxfrTo in H1.
apply Forall_app with (l1:=l) (l2:=d2); assumption.
apply IH; assumption.
Qed.

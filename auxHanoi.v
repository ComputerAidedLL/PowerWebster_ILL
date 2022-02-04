(*** ************************ ***)
(*** TOWERS OF HANOI - EXTRAS ***)
(*** ************************ ***)

(* James Power * James.Power@May.ie * http://www.cs.may.ie/~jpower/ *)
(* Dept. of Computer Science, NUI Maynooth, Co. Kildare, Ireland.   *)

(* This file is part of the Towers of Hanoi in ILL example.
 * Here we define some auxiliary lemmas to help "clean up" the
 * main proof - they mostly relate to manipulating the conjunction
 * of (three) linear predicates that represents the state
 * The lemmas are:
 *   S23/Swap23: Used for MOVE n-1 discs from peg P1 to peg P2 
 *   Lose2 :     Used when we TXFR 1 disc from peg P1 to peg P3 
 *   S21/Swap21: Used for MOVE n-1 discs from peg P2 to peg P3 
 *)

Require Export extraLL.

Remark S23
  (P1 P2 P3:ILinProp): ([P1***P2***P3] |- P1***P3***P2).
Proof.
intros.
linsplit.
leftapply TimesComm; apply Identity.
Qed.

Lemma Swap23
  (P1 P2 P3 C1 C2 C3:ILinProp):
  ([P1***P3***P2] |- C1***C3***C2) -> ([P1***P2***P3] |- C1***C2***C3).
Proof.
intros.
lincut (P1***P3***P2). apply S23.
lincut (C1***C3***C2); apply S23.
Qed.


Lemma Lose2
  (P1 P2 P3 C1 C3:ILinProp):
  ([P1***P3] |- C1***C3) -> ([P1***P2***P3] |- C1***P2***C3).
Proof.
intros.
leftapply Swap23.
leftapply TimesAssocR. apply RTimesAssocR.
linsplit. assumption.
Qed.



Remark S21
  (P1 P2 P3:ILinProp): ([P1***P2***P3] |- P2***P1***P3).
Proof.
intros.
leftapply TimesComm. leftapply TimesAssocL. linsplit.
leftapply TimesComm. apply Identity.
Qed.


Lemma Swap21
  (P1 P2 P3 C1 C2 C3:ILinProp):
  ([P2***P1***P3] |- C2***C1***C3) -> ([P1***P2***P3] |- C1***C2***C3).
Proof.
intros.
lincut (P2***P1***P3).
apply S21.
lincut (C2***C1***C3); apply S21.
Qed.

(*** ********************* ***)
(*** LINEAR LOGIC - EXTRAS ***)
(*** ********************* ***)

(* James Power * James.Power@May.ie * http://www.cs.may.ie/~jpower/ *)
(* Dept. of Computer Science, NUI Maynooth, Co. Kildare, Ireland.   *)

(* This file defines some auxiliary ILL tactics and proofs,
 * in particular:
 *   tactics LeftApply, LinCut, LinSplit and ChangeTo
 *   lemmas relating to associativity and communtativity of Times
 *)


(*** TACTIC DEFINITONS ***)

Lemma AddNilFront : 
  (P:(list ILinProp))(C:ILinProp) (Empty ^ P |- C) -> (P |- C).
Auto.
Qed.

Tactic Definition LeftApply [$myTac] :=
  [<:tactic:<((Apply $myTac) Orelse (Apply AddNilFront; Apply $myTac; Rewrite <- app_nil_front))>>].


Lemma AddNilEnd : 
  (P:(list ILinProp))(C:ILinProp) (P ^ Empty |- C) -> (P |- C).
Intros; Rewrite <- (app_nil_end P) in H; Auto.
Qed.

Tactic Definition LinCut [$cutHyp] :=
  [<:tactic:<((Apply Cut with A:=$cutHyp) Orelse (Apply AddNilFront; Apply Cut with A:=$cutHyp; [Try Assumption | Rewrite <- app_nil_front]))>>].


Tactic Definition LinSplit  :=
  [<:tactic:<LeftApply TimesLeft; Apply TimesRight; Try (Apply Identity)>>].


Tactic Definition ChangeTo [$newGoal] := 
[<:tactic:<Cut $newGoal; [Simpl; Repeat (Rewrite app_ass); Simpl; Repeat (Rewrite ass_app); Simpl; Auto | Idtac]>>].

Lemma ExchList : (L1,L2,D1,D2:(list ILinProp))(C:ILinProp)
  ((D1 ^ L1 ^ L2 ^ D2 |- C) -> (D1 ^ L2 ^ L1 ^ D2 |- C)).
Proof.
Induction L1; Induction L2; Clear L1 L2.
(*1*) Auto.
(*2*) Auto.
(*3*) Auto.
(*4*) Intros a' l' H' D1 D2 C ORIG.
ChangeTo ((D1^`a')^l'^(cons a l)^D2 |- C).
Apply H'.
ChangeTo (D1^`a'^`a^(l^l'^D2) |- C).
Apply Exchange.
ChangeTo ((D1^`a)^`a'^l^(l'^D2) |- C).
Apply H.
ChangeTo (D1^((cons a l)^((cons a' l')^D2)) |- C).
Exact ORIG.
Qed.



(*** AUXILIARY LEMMAS RELATING TO THE TIMES OPERATOR ***)

Lemma TimesLeftInv :  (G : (list ILinProp))(A,B,S : ILinProp)
  (G ^ `(A**B) |- S) -> (G ^ `A ^ `B |- S).
Proof.
Intros.
LinCut A**B.
LeftApply TimesRight; Apply Identity.
Assumption.
Qed.


Section TimesRules.

Variable G : (list ILinProp).
Variable A,B,C,S : ILinProp.

Lemma TimesComm :
  (G ^ `(A**B) |- S) -> (G ^ `(B**A) |- S).
Proof.
Intros.
Apply TimesLeft.
Rewrite (app_nil_end `A); Apply Exchange; Rewrite <- app_nil_end.
Apply TimesLeftInv.
Assumption.
Qed.

Lemma TimesAssocL :  
  (G ^ `(A**(B**C)) |- S) -> (G ^ `((A**B)**C) |- S).
Proof.
Intros.
Apply TimesLeft.
Rewrite (app_nil_end `C). 
Apply ExchList.
ChangeTo ((G^`C)^`(A**B) |- S).
Apply TimesLeft.
ChangeTo (G^`C^(`A^`B)^Empty |- S).
Apply ExchList.
ChangeTo ((G^`A)^`B^ `C |- S).
Apply TimesLeftInv.
ChangeTo (G^`A^`(B**C) |- S).
Apply TimesLeftInv.
Assumption.
Qed.

Lemma TimesAssocR :  
  (G ^ `((A**B)**C) |- S) -> (G ^ `(A**(B**C)) |- S).
Proof.
Intros.
Apply TimesLeft.
ChangeTo ((G^`A)^`(B**C) |- S).
Apply TimesLeft.
ChangeTo (G^(`A^`B)^`C^Empty |- S).
Apply ExchList.
ChangeTo ((G^`C)^`A^`B |- S).
Apply TimesLeftInv.
ChangeTo (G^`C^`(A**B)^Empty |- S).
Apply ExchList.
ChangeTo (G^`(A**B)^`C |- S).
Apply TimesLeftInv.
Assumption.
Qed.

End TimesRules.



Section RightTimesRules.

Variable G : (list ILinProp).
Variable A,B,C,S : ILinProp.

Lemma RTimesComm :
  (G |- (A**B)) -> (G |- (B**A)).
Proof.
Intros.
LinCut A**B; (LeftApply TimesComm; Apply Identity).
Qed.

Lemma RTimesAssocL :  
  (G |- (A**(B**C))) -> (G |- ((A**B)**C)).
Proof.
Intros.
LinCut A**(B**C); (LeftApply TimesAssocR; Apply Identity).
Qed.

Lemma RTimesAssocR :  
  (G |- ((A**B)**C)) -> (G |- (A**(B**C))).
Proof.
Intros.
LinCut (A**B)**C; (LeftApply TimesAssocL; Apply Identity).
Qed.

End RightTimesRules.





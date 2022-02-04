(*** ********************* ***)
(*** LINEAR LOGIC - EXTRAS ***)
(*** ********************* ***)

(* James Power * James.Power@May.ie * http://www.cs.may.ie/~jpower/ *)
(* Dept. of Computer Science, NUI Maynooth, Co. Kildare, Ireland.   *)

(* This file defines some auxiliary ILL tactics and proofs,
 * in particular:
 *   tactics LeftApply, LinCut, LinSplit and ChangeTo
 *   lemmas relating to associativity and commutativity of Times
 *)

Require Export ILL.


(*** TACTIC DEFINITONS ***)

Lemma AddNilFront (P: list ILinProp)(C:ILinProp): (Empty ++ P |- C) -> (P |- C).
Proof.
auto.
Qed.

Ltac leftapply t := apply t + (apply AddNilFront; apply t; rewrite app_nil_l).

Lemma AddNilEnd (P: list ILinProp)(C:ILinProp): (P ++ Empty |- C) -> (P |- C).
Proof.
intros; rewrite (app_nil_r P) in H; auto.
Qed.

Ltac lincut H := apply Cut with (A := H) + (apply AddNilFront; apply Cut with (A := H); [try assumption | rewrite app_nil_l]).

Ltac linsplit := leftapply TimesLeft; apply TimesRight; try (apply Identity).

Ltac changeto A := cut A; [simpl; rewrite ? app_assoc; simpl; rewrite <- ? app_assoc; simpl; auto | ].

Lemma ExchList (L1 L2 D1 D2: list ILinProp)(C:ILinProp):
  ((D1 ++ L1 ++ L2 ++ D2 |- C) -> (D1 ++ L2 ++ L1 ++ D2 |- C)).
Proof.
revert L2 D1 D2.
induction L1 as [|a l H]; induction L2 as [|a' l' H'].
(*1*) auto.
(*2*) auto.
(*3*) auto.
(*4*) intros D1 D2 ORIG.
changeto ((D1++[a'])++l'++(cons a l)++D2 |- C).
apply H'.
changeto (D1++[a']++[a]++(l++l'++D2) |- C).
apply Exchange.
changeto ((D1++[a])++[a']++l++(l'++D2) |- C).
apply H.
changeto (D1++((cons a l)++((cons a' l')++D2)) |- C).
exact ORIG.
Qed.



(*** AUXILIARY LEMMAS RELATING TO THE TIMES OPERATOR ***)

Lemma TimesLeftInv (G : list ILinProp)(A B S : ILinProp):
  (G ++ [A***B] |- S) -> (G ++ [A] ++ [B] |- S).
Proof.
intros.
lincut A***B.
apply TimesRight; apply Identity.
assumption.
Qed.


Section TimesRules.

Variable G : list ILinProp.
Variable A B C S : ILinProp.

Lemma TimesComm :
  (G ++ [A***B] |- S) -> (G ++ [B***A] |- S).
Proof.
intros.
apply TimesLeft.
rewrite <- (app_nil_r [A]); apply Exchange; rewrite app_nil_r.
apply TimesLeftInv.
assumption.
Qed.

Lemma TimesAssocL :
  (G ++ [A***(B***C)] |- S) -> (G ++ [(A***B)***C] |- S).
Proof.
intros.
apply TimesLeft.
rewrite <- (app_nil_r [C]).
apply ExchList.
changeto ((G++[C])++[A***B] |- S).
apply TimesLeft.
changeto (G++[C]++([A]++[B])++Empty |- S).
apply ExchList.
changeto ((G++[A])++[B]++[C] |- S).
apply TimesLeftInv.
changeto (G++[A]++[B***C] |- S).
apply TimesLeftInv.
assumption.
Qed.

Lemma TimesAssocR :
  (G ++ [(A***B)***C] |- S) -> (G ++ [A***(B***C)] |- S).
Proof.
intros.
apply TimesLeft.
changeto ((G++[A])++[B***C] |- S).
apply TimesLeft.
changeto (G++([A]++[B])++[C]++Empty |- S).
apply ExchList.
changeto ((G++[C])++[A]++[B] |- S).
apply TimesLeftInv.
changeto (G++[C]++[A***B]++Empty |- S).
apply ExchList.
changeto (G++[A***B]++[C] |- S).
apply TimesLeftInv.
assumption.
Qed.

End TimesRules.



Section RightTimesRules.

Variable G : list ILinProp.
Variable A B C S : ILinProp.

Lemma RTimesComm :
  (G |- A***B) -> (G |- B***A).
Proof.
intros.
lincut A***B; (leftapply TimesComm; apply Identity).
Qed.

Lemma RTimesAssocL :
  (G |- A***(B***C)) -> (G |- (A***B)***C).
Proof.
intros.
lincut A***(B***C); (leftapply TimesAssocR; apply Identity).
Qed.

Lemma RTimesAssocR :
  (G |- (A***B)***C) -> (G |- A***(B***C)).
Proof.
intros.
lincut (A***B)***C; (leftapply TimesAssocL; apply Identity).
Qed.

End RightTimesRules.

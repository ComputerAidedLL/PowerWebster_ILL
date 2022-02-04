(*** *********************** ***)
(*** BLOCKS WORLD EXAMPLE ***)
(*** *********************** ***)

(* James Power * James.Power@May.ie * http://www.cs.may.ie/~jpower/ *)
(* Dept. of Computer Science, NUI Maynooth, Co. Kildare, Ireland.   *)


(* Need at least the following before this file: ILL.v, extraLL.v *)
Require Import extraLL.


Parameter Block:Set.

(* Five predicates desribing the state:
 *   (on x y)  - true if block x is on block y
 *   (table x) - true if block x is on the table (no block beneath it) 
 *   (clear x) - true if there's nothing on top of block x 
 *   (holds x) - true if the robot arm holds block x 
 *   empty     - true if the robot arm is empty 
 *)

Parameter on    : Block -> Block -> ILinProp.
Parameter table : Block -> ILinProp.
Parameter clear : Block -> ILinProp.
Parameter holds : Block -> ILinProp.
Parameter empty : ILinProp.



(* The two basic actions:
 *   get - picks up a block (from the table, or from another block)
 *   put - drops a block (on the table, or on another block)
 *)

Axiom get :
  forall (x y:Block),
  ([empty *** (clear x)]
|- (holds x) *** (((table x) --o One) &&& ((on x y) --o (clear y)))).

Axiom put :
  forall (x y:Block),
  ([holds x]
|- empty *** (clear x) ***  ((table x) &&& ((clear y) --o (on x y)))).


(* Now four special cases of these two actions *)

(* 1. Get a block x which is currently on some block y *)
Lemma geton 
  (x y:Block) :
  ([empty *** (clear x) *** (on x y)]  |- (holds x) *** (clear y)).
Proof.
leftapply TimesAssocR. leftapply TimesComm. leftapply TimesLeft.
lincut (holds x)***((table x)--oOne)&&&((on x y)--o(clear y)).
apply get.
leftapply TimesLeft.
leftapply ExchList.
apply TimesRight.
apply Identity.
leftapply WithLeft2.
apply AddNilFront. leftapply ExchList.
leftapply ImpliesLeft.
apply Identity.
(simpl; apply Identity).
Qed.

(* 2. Get block x which is currently on the table *)
Lemma gettb
  (x:Block) :
  ([empty *** (clear x) *** (table x)]  |- (holds x)).
Proof.
leftapply TimesAssocR. leftapply TimesComm. leftapply TimesLeft.
cut Block; [intros y | auto]. (* introduces y *)
lincut (holds x)***((table x)--oOne)&&&((on x y)--o(clear y)).
apply get.
leftapply TimesLeft.
rewrite app_assoc. leftapply WithLeft1. 
rewrite <- app_assoc. leftapply ImpliesLeft.
apply Identity.
leftapply OneLeft.
apply Identity.
Qed.

(* 3. Put block x (which the arm is holding) onto block y *)
Lemma puton
  (x y:Block) :
  ([(holds x) *** (clear y)] |- empty *** (clear x) *** (on x y)).
Proof.
intros.
leftapply TimesComm. leftapply TimesLeft.
lincut (empty***(clear x)***(table x)&&&((clear y)--o(on x y))).
apply put.
leftapply TimesLeft.
rewrite app_assoc. leftapply TimesLeft.
rewrite app_assoc. leftapply WithLeft2.
changeto ([clear y] ++ ([empty] ++ [clear x]) ++ [(clear y)--o(on x y)] |- empty *** (clear x) *** (on x y)).
leftapply ImpliesLeft.
apply Identity.
rewrite <- app_assoc.
apply TimesRight; [ apply Identity | (apply TimesRight; apply Identity)].
Qed.

(* 4. Put block x (which the arm is holding) onto the table *)
Lemma puttb
  (x:Block) :
  ([holds x]  |- empty *** (clear x) *** (table x)).
Proof.
intros.
cut Block; [intros y | auto]. (* introduces y *)
lincut (empty***(clear x)***(table x)&&&((clear y)--o(on x y))).
apply put.
leftapply TimesLeft.
apply TimesRight.
apply Identity.
leftapply TimesLeft.
apply TimesRight.
apply Identity.
leftapply WithLeft1.
apply Identity.
Qed.



(*** The example: swapping the order of a and b
 *
 *          +---+                   +---+
 *          | b |                   | a |
 *          +---+                   +---+
 *          +---+  +---+            +---+  +---+
 *          | a |  | c |            | b |  | c |
 *          +---+  +---+            +---+  +---+
 *          Before State            After State
 *)


Section BlocksExample.

Variable a b c:Block.

(* Six auxiliary lemmas, then the main theorem SwapAB *)

(* 1. Get rid of the info relating to block C (into Top) *)
Lemma IgnoreC :
  ([empty***(clear b)***(on b a)***(table a)***(table c)***(clear c)]
 |- empty***(clear b)***(on b a)***(table a)***Top).
Proof.
do 3 (leftapply TimesAssocR).
do 3 (apply RTimesAssocR).
linsplit.  apply TopRight.
Qed.

(* 2. Pick up block b *)
Lemma PickUpB :
  ([empty***(clear b)***(on b a)***(table a)***Top]
 |- (holds b)***(clear a)***(table a)***Top).
Proof.
do 2 (leftapply TimesAssocR).  (apply RTimesAssocR).
linsplit.
leftapply TimesAssocL; apply geton.
Qed.

(* 3. Drop block b onto the table *)
Lemma DropB :
  ([(holds b)***(clear a)***(table a)***Top]
 |- empty***(table b)***(clear b)***(clear a)***(table a)***Top).
Proof.
do 2 (apply RTimesAssocR).
linsplit.
lincut empty***(clear b)***(table b).
apply puttb.
apply RTimesAssocL; linsplit.
leftapply TimesComm; apply Identity.
Qed.

(* 4. Pick up block a *)
Lemma PickUpA :
  ([empty***(table b)***(clear b)***(clear a)***(table a)***Top]
 |- (table b)***(clear b)***(holds a)***Top).
Proof.
leftapply TimesComm.
leftapply TimesAssocL. linsplit.
leftapply TimesAssocL. linsplit.
leftapply TimesComm. do 2 (leftapply TimesAssocR). linsplit.
leftapply TimesAssocL.
apply gettb.
Qed.

(* 5. Drop block a onto block b *)
Lemma DropA :
  ([(table b)***(clear b)***(holds a)***Top]
|- (table b)***empty***(on a b)***(clear a)***Top).
Proof.
linsplit.
leftapply TimesAssocR. do 2 (apply RTimesAssocR). linsplit.
lincut (empty *** (clear a) *** (on a b)).
leftapply TimesComm; apply puton.
apply RTimesAssocL.
linsplit.
apply RTimesComm.
apply Identity.
Qed.

(* 6. Get rid of extra info into Top *)
Lemma TidyUp :
  ([(table b)***empty***(on a b)***(clear a)***Top]
 |- (on a b)***Top).
Proof.
do 2 (leftapply TimesAssocR). leftapply TimesComm.
leftapply TimesAssocR. leftapply TimesComm.
leftapply TimesLeft.
linsplit.
apply TopRight.
Qed.


(* The theorem: cut-and-apply _forwards_ through the states *)

Theorem SwapAB :
  ([empty *** (clear b) *** (on b a) *** (table a) *** (table c) *** (clear c)]
|-
  (on a b) *** Top).
Proof.
lincut ((empty)***(clear b)***(on b a)***(table a)***Top). 
apply IgnoreC.
lincut ((holds b)***(clear a)***(table a)***Top). 
apply PickUpB.
lincut (empty***(table b)***(clear b)***(clear a)***(table a)***Top). 
apply DropB.
lincut ((table b)***(clear b)***(holds a)***Top). 
apply PickUpA.
lincut ((table b)***empty***(on a b)***(clear a)***Top). 
apply DropA.
apply TidyUp.
Qed.

End BlocksExample.

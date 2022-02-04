(*** *********************** ***)
(*** TOWERS OF HANOI EXAMPLE ***)
(*** *********************** ***)

(* James Power * James.Power@May.ie * http://www.cs.may.ie/~jpower/ *)
(* Dept. of Computer Science, NUI Maynooth, Co. Kildare, Ireland.   *)

(* This file is part of the Towers of Hanoi in ILL example
 * In it, we define the discs and the "smaller" relation
 * as well as some lemmas relating to quantification over disc-lists
 *
 * See also: discs.v, auxHanoi.v
 *)


(*************)
(*** POLES ***)
(*************)

Parameter Pole : Set.
Parameter onPole : Pole -> (list Disc) -> ILinProp.

Definition empty : Pole -> ILinProp := 
  [p:Pole] (onPole p (nil Disc)).


(*********************)
(*** THE ALGORITHM ***)
(*********************)

(* Assume we can move one disc *)
Axiom Txfr : 
  (p1,p2:Pole)
  (f:Disc)(fs,ts:(list Disc)) (canTxfrTo f ts) ->
  (`((onPole p1 (cons f fs))**(onPole p2 ts))
|-
  ((onPole p1 fs) ** (onPole p2 (cons f ts)))).


(* Now prove that this scales up to n discs ... *)

(* The strategy is to use a Cut to introduce the intermediate states
 * then get to them using Move, Txfr and Move, in that order.
 * Each of these three applications has three sub-steps:
 *  a) Re-arrange the conjunction into the correct form
 *  b) Apply Txfr or Move, as appropriate
 *  c) Prove that the state-invariant predicates still hold true
 *)

Lemma Move :
  (dTop,dBot:(list Disc))
  (p1,p2,p3:Pole) (d2,d3:(list Disc)) 
  (ordered dTop) -> 
  (canMoveTo dTop dBot) -> (canMoveTo dTop d2) -> (canMoveTo dTop d3) ->
  (`((onPole p1 (dTop^dBot))**(onPole p2 d2)**(onPole p3 d3))
|-
  (onPole p1 dBot) ** (onPole p2 d2) ** (onPole p3 (dTop^d3))).
Proof.
  Intros dTop; Apply rev_ind with l:=dTop. (* Reverse Induction on dTop *)


  (* Base Case: dTop is nil *)
  Intros ; Simpl; Apply Identity.


  (* Inductive Case: dTop is (cons d ds) *)
  Intros d ds MOVE dBot p1 p2 p3 d2 d3 ORD.
  Unfold canMoveTo; Intros CM1 CM2 CM3.

  (* Mark out the "states" we're going to go through *)
  LinCut (onPole p1 dBot)**(onPole p2 (ds^d2))**(onPole p3 (`d^d3)).
  LinCut (onPole p1 (`d^dBot))**(onPole p2 (ds^d2))**(onPole p3 d3).

  (* Step 1: (Move ds from p1 to p2) *)
  Rewrite (app_ass ds).  Apply Swap23.
  Apply MOVE;
    Try (Unfold canMoveTo; Apply AllCat with l1:=ds l2:=`d; Assumption).
  Apply OrdCat with d1:=ds d2:=`d; Assumption.
  Apply CanMoveApp.
  Apply OrdMove; Assumption.
  (Unfold canMoveTo; Apply AllCat with l1:=ds l2:=`d; Assumption).

  (* Step 2: (Txfr d  from p1 to p3) *)
  Apply Lose2.  Simpl.
  Apply (Txfr p1 p3).
  Apply OneCat with a:=d l:=ds; Assumption.

  (* Step 3: (Move ds from p2 to p3) *)
  Apply Swap21.  Rewrite app_ass.
  Apply MOVE;
    Try (Unfold canMoveTo; Apply AllCat with l1:=ds l2:=`d; Assumption).
  Apply OrdCat with d1:=ds d2:=`d; Assumption.
  Rewrite SepCons; Apply CanMoveApp.
  Apply OrdMove; Assumption.
  (Unfold canMoveTo; Apply AllCat with l1:=ds l2:=`d; Assumption).
Qed.



Theorem Hanoi :
  (p1,p2,p3:Pole) (ds:(list Disc))
  (ordered ds) ->
  (`((onPole p1 ds) ** (empty p2) ** (empty p3))
|-
  (empty p1) ** (empty p2) ** (onPole p3 ds)).
Proof.
Intros. Rewrite (app_nil_end ds). Unfold empty.
Apply Move; Try (Apply CanMoveEmpty).
Assumption.
Qed.



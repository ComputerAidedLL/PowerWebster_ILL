(*** ******************************* ***)
(*** LINEAR LOGIC - BASIC DEFINITONS ***)
(*** ******************************* ***)

(* James Power * James.Power@May.ie * http://www.cs.may.ie/~jpower/ *)
(* Dept. of Computer Science, NUI Maynooth, Co. Kildare, Ireland.   *)

(**********************************)
(***** The Linear Connectives *****)
(**********************************)
Inductive ILinProp :=
| Implies : (ILinProp) -> (ILinProp) -> ILinProp
| OfCourse : (ILinProp) -> ILinProp
| One : ILinProp
| Plus : (ILinProp) -> (ILinProp) -> ILinProp
| Times : (ILinProp) -> (ILinProp) -> ILinProp
| Top : ILinProp
| With : (ILinProp) -> (ILinProp) -> ILinProp
| Zero : ILinProp
| Exists (A:Set): (A->ILinProp) -> ILinProp
.

Notation "! c" := (OfCourse c) (at level 2).
Infix "***" := Times (at level 6, right associativity).
Infix "&&&" := With (at level 6, right associativity).
Infix "+++" := Plus (at level 7).
Infix "--o" := Implies (at level 8).



(*******************************************)
(***** The Linear Consequence Operator *****)
(*****               and               *****)
(*****    Natural Deduction Rules      *****)
(*******************************************)

From Stdlib Require Export List.
Export ListNotations.
Notation Empty := (@nil _).

Reserved Notation "c1 |- c2" (at level 65).

Inductive LinCons : (list ILinProp) -> ILinProp -> Prop :=
(* Structural Rules *)
 Identity (A:ILinProp):
  ([A] |- A)
| Exchange (A B C : ILinProp)(D1 D2 : list ILinProp):
  ((D1 ++ [A] ++ [B] ++ D2 |- C) -> (D1 ++ [B] ++ [A] ++ D2 |- C))
| Cut (A C : ILinProp)(D1 D2 : list ILinProp):
  ((D1 |- A) -> (D2 ++ [A] |- C) -> (D2 ++ D1 |- C))

(* Multiplicative Conjunction *)
| TimesRight (A B : ILinProp)(D1 D2 : list ILinProp):
  ((D1 |- A) -> (D2 |- B) -> (D1 ++ D2 |- A *** B))
| TimesLeft (A B C : ILinProp)(D : list ILinProp):
  ((D ++ [A] ++ [B] |- C) -> (D ++ [A***B] |- C))
| OneRight :
  (Empty |- One)
| OneLeft (C : ILinProp)(D : list ILinProp):
  ((D |- C) -> (D ++ [One] |- C))
(* (Multiplicative) Implication *)
| ImpliesRight (A B : ILinProp)(D : list ILinProp):
  ((D ++ [A] |- B) -> (D |- A --o B)) 
| ImpliesLeft (A B C : ILinProp)(D1 D2 : list ILinProp):
  ((D1 |- A) -> (D2 ++ [B] |- C) -> (D1 ++ D2 ++ [A --o B]  |- C))

(* Additive Conjunction *)
| WithRight (A B : ILinProp)(D : list ILinProp):
  ((D |- A) -> (D |- B) -> (D |- (A&&&B)))
| WithLeft1 (A B C : ILinProp)(D : list ILinProp):
  ((D ++ [A] |- C) -> (D ++ [A&&&B] |- C))
| WithLeft2 (A B C : ILinProp)(D : list ILinProp):
  ((D ++ [B] |- C) -> (D ++ [A&&&B] |- C))
| TopRight (D : list ILinProp):
  (D |- Top)
(* Additive Disjunction *)
| PlusRight1 (A B : ILinProp)(D : list ILinProp):
  ((D |- A) -> (D |- (A+++B)))
| PlusRight2 (A B : ILinProp)(D : list ILinProp):
  ((D |- B) -> (D |- (A+++B)))
| PlusLeft (A B C : ILinProp)(D : list ILinProp):
  ((D ++ [A] |- C)  -> (D ++ [B] |- C) -> (D ++ [A+++B] |- C))
| ZeroLeft (C : ILinProp)(D : list ILinProp):
  (D ++ [Zero] |- C)

(* Modalities *)
| Weakening (A C : ILinProp)(D : list ILinProp):
  ((D |- C) -> (D ++ [!A] |- C))
| Contraction (A C : ILinProp)(D : list ILinProp):
  ((D ++ [!A] ++ [!A] |- C) -> (D ++ [!A] |- C))
| Dereliction (A C : ILinProp)(D : list ILinProp):
  ((D ++ [A] |- C) -> (D ++ [!A] |- C))
| Promotion (A C : ILinProp)(D : list ILinProp):
  (([!A] |- C) -> ([!A] |- !C))

where "c1 |- c2" := (LinCons c1 c2).

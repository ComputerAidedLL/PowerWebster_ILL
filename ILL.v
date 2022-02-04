(*** ******************************* ***)
(*** LINEAR LOGIC - BASIC DEFINITONS ***)
(*** ******************************* ***)

(* James Power * James.Power@May.ie * http://www.cs.may.ie/~jpower/ *)
(* Dept. of Computer Science, NUI Maynooth, Co. Kildare, Ireland.   *)

(**********************************)
(***** The Linear Connectives *****)
(**********************************)
Inductive ILinProp : Set :=
| Implies : (ILinProp) -> (ILinProp) -> ILinProp
| OfCourse : (ILinProp) -> ILinProp
| One : ILinProp
| Plus : (ILinProp) -> (ILinProp) -> ILinProp
| Times : (ILinProp) -> (ILinProp) -> ILinProp
| Top : ILinProp
| With : (ILinProp) -> (ILinProp) -> ILinProp
| Zero : ILinProp
| Exists : (A:Set)(A->ILinProp) -> ILinProp
.

Grammar command command2 :=
  OfCourse [ "!" command2($c) ] -> [<<(OfCourse $c)>>].
Syntax constr level 2:
  POfCourse [<<(OfCourse $c)>>] -> [ "!" $c ].

Grammar command  command6 :=
  Times [ command5($c1) "**" command6($c2) ] -> [<<(Times $c1 $c2)>>]
| With [command5($c1) "&&" command6($c2) ] -> [<<(With $c1 $c2)>>].
Syntax constr level 6:
  PTimes [<<(Times $c1 $c2)>>] -> [ $c1:L "**" $c2:E ].
Syntax constr level 6:
  PWith [<<(With $c1 $c2)>>] -> [ $c1:L "&&" $c2:E ].

Grammar command command7 :=
  Plus [ command6($c1) "++" command7($c2) ] -> [<<(Plus $c1 $c2)>>].
Syntax constr level 7:
  PPlus [<<(Plus $c1 $c2)>>] -> [ $c1:L "++" $c2:E ].

Grammar command command8 :=
  Implies [ command7($c1) "-o" command8($c2) ] -> [<<(Implies $c1 $c2)>>].
Syntax constr level 8:
  PImplies [<<(Implies $c1 $c2)>>] -> [ $c1:L "-o" $c2:E ].



(*******************************************)
(***** The Linear Consequence Operator *****)
(*****               and               *****)
(*****    Natural Deduction Rules      *****)
(*******************************************)

Load moreLists.

Grammar command command9 :=
  LinCons [ command8($c1) "|-" command9($c2) ] -> [<<(LinCons $c1 $c2)>>].
Syntax constr level 9:
  PLinCons [<<(LinCons $t1 $t2)>>] -> [ $t1 " |- " $t2 ].

Inductive LinCons : (list ILinProp) -> ILinProp -> Prop := 
(* Structural Rules *)
 Identity : 
  (A:ILinProp)  
  (`A |- A)
| Exchange : 
  (A,B,C : ILinProp)(D1,D2 : (list ILinProp))
  ((D1 ^ `A ^ `B ^ D2 |- C) -> (D1 ^ `B ^ `A ^ D2 |- C))
| Cut : 
  (A,C : ILinProp)(D1,D2 : (list ILinProp))
  ((D1 |- A) -> (D2 ^ `A |- C) -> (D2 ^ D1 |- C))

(* Multiplicative Conjunction *)
| TimesRight :  
  (A,B : ILinProp)(D1,D2 : (list ILinProp))
  ((D1 |- A) -> (D2 |- B) -> (D1 ^ D2 |- A ** B)) 
| TimesLeft : 
  (A,B,C : ILinProp)(D : (list ILinProp)) 
  ((D ^ `A ^ `B |- C) -> (D ^ `(A**B) |- C))
| OneRight :  
  (Empty |- One)
| OneLeft : 
  (C : ILinProp)(D : (list ILinProp)) 
  ((D |- C) -> (D ^ `One |- C))
(* (Multiplicative) Implication *)
| ImpliesRight :  
  (A,B : ILinProp)(D : (list ILinProp))
  ((D ^ `A |- B) -> (D |- A -o B)) 
| ImpliesLeft :  
  (A,B,C : ILinProp)(D1,D2 : (list ILinProp)) 
  ((D1 |- A) -> (D2 ^ `B |- C) -> (D1 ^ D2 ^ `(A -o B)  |- C))

(* Additive Conjunction *)
| WithRight :  
  (A,B : ILinProp)(D : (list ILinProp)) 
  ((D |- A) -> (D |- B) -> (D |- (A&&B)))
| WithLeft1:  
  (A,B,C : ILinProp)(D : (list ILinProp)) 
  ((D ^ `A |- C) -> (D ^ `(A&&B) |- C))
| WithLeft2:  
  (A,B,C : ILinProp)(D : (list ILinProp)) 
  ((D ^ `B |- C) -> (D ^ `(A&&B) |- C))
| TopRight :  
  (D : (list ILinProp)) 
  (D |- Top)
(* Additive Disjunction *)
| PlusRight1 :  
  (A,B : ILinProp)(D : (list ILinProp)) 
  ((D |- A) -> (D |- (A++B)))
| PlusRight2 :  
  (A,B : ILinProp)(D : (list ILinProp)) 
  ((D |- B) -> (D |- (A++B)))
| PlusLeft :  
  (A,B,C : ILinProp)(D : (list ILinProp)) 
  ((D ^ `A |- C)  -> (D ^ `B |- C) -> (D ^ `(A++B) |- C))
| ZeroLeft :  
  (C : ILinProp)(D : (list ILinProp)) 
  (D ^ `Zero |- C)

(* Modalities *)
| Weakening :  
  (A,C : ILinProp)(D : (list ILinProp)) 
  ((D |- C) -> (D ^ `!A |- C))
| Contraction :  
  (A,C : ILinProp)(D : (list ILinProp)) 
  ((D ^ `!A ^ `!A |- C) -> (D ^ `!A |- C))
| Dereliction :  
  (A,C : ILinProp)(D : (list ILinProp)) 
  ((D ^ `A |- C) -> (D ^ `!A |- C))
| Promotion :  
  (A,C : ILinProp)(D : (list ILinProp)) 
  ((`!A |- C) -> (`!A |- !C)).



(* Some syntactic sugar *)
Require PolyList.
Require PolyListSyntax.
Implicit Arguments On.

Syntactic Definition Empty := (nil ?).

(* For convenience, define `x to be the list containing just x *)
Grammar command command2 :=
  ListOne  [ "`" command2($c) ] -> [<<(cons $c Empty)>>].
Syntax constr level 2:
  POneH [<<(cons $t1 (nil ?))>>] -> [ "`" $t1 ].

Syntax constr level 7:
  PManyH [<<(app $t1 $t2)>>] -> [ $t1:L "^" $t2:E ].

Section MoreLists.

Variable A : Set.

Lemma app_nil_front : (l:(list A)) l=((nil A)^l).
Proof.
Auto. 
Qed.

Lemma appEQ : (l,m,n:(list A)) (m=n) -> (l^m)=(l^n).
Proof.
Intros l m n EQ.Rewrite EQ.Auto.
Qed.

Lemma appEQR : (l,m,n:(list A)) (m=n) -> (m^l)=(n^l).
Proof.
Intros l m n EQ.Rewrite EQ.Auto.
Qed.

Lemma SepCons : (a:A)(l:(list A)) (cons a l)=(`a^l).
Proof.
(Intros; Simpl; Auto).
Qed.

Lemma TwoNils : (Z1,Z2:(list A)) (Z1^Z2)=(Empty^Z1^Z2^Empty).
Proof.
Intros; Simpl; Rewrite <- app_nil_end; Auto.
Qed.


End MoreLists.


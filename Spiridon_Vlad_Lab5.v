Require Import String.
Check String.
(* Check "a". *)
Open Scope string_scope.
Check "a".

(*EX 1*)
Inductive AExp :=
| var : string -> AExp
| num : nat -> AExp
| add : AExp -> AExp -> AExp
| mul : AExp -> AExp -> AExp
| div : AExp -> AExp -> AExp
| sub : AExp -> AExp -> AExp.

Coercion var : string >-> AExp.
Coercion num : nat >-> AExp.

Check (add (num 2) (add (var "x") (div (num 2) (var "y")))).
Check (add 2 (add "x" (div 2 "y"))).

Notation "A +' B" := (add A B)
                       (at level 50, left associativity).

Notation "A -' B" := (sub A B)
                       (at level 50, left associativity).
Notation "A *' B" := (mul A B)
                       (at level 40, left associativity).

Notation "A /' B" := (div A B)
                       (at level 40, left associativity).

Check (add 2 (add "x" (div 2 "y"))).

Check 2 +' ("x" +' 2 /' "y").
Set Printing All.
Check 2 -' ("x" +' 2 /' "y").
Check 2 -' "x" /' "y".
Check "x" /' "y" +' 2.
Check "x" /' "y" /' "z".
Unset Printing All.

(*EX 2*)
Inductive Cond :=
| base : bool -> Cond
| bnot : Cond -> Cond
| beq  : AExp -> AExp -> Cond
| less : AExp -> AExp -> Cond
| band : Cond -> Cond -> Cond.

Coercion base : bool >-> Cond.
Notation "'!' B" := (bnot B) (at level 65, right associativity).
Notation "A <' B" := (less A B) (at level 60).
Notation "A =' B" := (beq A B) (at level 60).
Notation "A >' B" := (less B A) (at level 60).
Notation "A <=' B" := (bnot (B >' A)) (at level 60).
Notation "A >=' B" := (bnot (B <' A)) (at level 60).
Notation "A &' B" := (band A B) (at level 70, right associativity).
Notation "A |' B" := (bnot(A &' (!B))) (at level 75, right associativity).

Check "x" <' "y".
Check "x" =' "y".
Check ! "x" =' "y".
Check "x" <' "y" &' "x" =' "y".
Check "x" <' "y" |' "x" =' "y".
Check "x" >' "y" |' "x" =' "y".
Check "x" >' "y".
Check 2 >' "y".
Check 3 >' "y".
Check "x" <=' "y".
Check 3 <=' "y".
Check 2 <=' "y".
Check "x" >=' "y".
Check 2 >=' "y".
Check 1 >=' "y".
Check !(! "x" <' "y" &' ! "x" =' "y").
Check ("x" <' "y" |' "x" =' "y") .

(*EX 3*)
Inductive Stmt :=
| skip : Stmt
| assign : string -> AExp -> Stmt
| seq : Stmt -> Stmt -> Stmt
| ite : Cond -> Stmt -> Stmt -> Stmt
| while : Cond -> Stmt -> Stmt.

(*EX 4*)
Notation "A ::= B" := (assign A B) (at level 20).
Notation "A ;; B" := (seq A B) (right associativity, at level 60).
Notation "'while' A 'do' B 'end'" := (while A B) (at level 70).
Notation "if A 'then' B 'else' C" := (ite A B C) (at level 80).

Definition compute_modulo (x y : string) :=
  "m" ::= 0 ;;
   while (x >' y) (
      x ::= x -' y
   );;
   ite (x =' y) ("m" ::= 0) ("m" ::= x) ;;
   "result" ::= "m".

(*EX 5*)
Definition Euclid_Scadere (x y : string) :=
  while (x >' y) do
    x ::= x -' y
  end ;;
  while (x <' y) do
    y ::= y -' x
  end ;;
  "RESULT" ::= x.

(*EX 6*)
Definition Fibonacci (n : string) :=
  "a" ::= 0 ;;
  "b" ::= 1 ;;
  "i" ::= 1 ;;
  while ("i" <' n) do
    "temp" ::= "b" ;;
    "b" ::= "a" + "b" ;;
    "a" ::= "temp" ;;
    "i" ::= "i" + 1
  end ;;
  "result" ::= "b".
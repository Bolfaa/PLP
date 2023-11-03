Require Import Nat.
Require Import List.
Import ListNotations.
(*EX 1*)
Inductive ArboreB ( T : Type) : Type :=
| NULL
| CONS (stanga: ArboreB T) (x : T) (dreapta : ArboreB T).
Arguments NULL {T}.
Arguments CONS {T}.

Definition A := CONS NULL 7 NULL.
Definition B := CONS  ( CONS NULL 5 NULL) 12 ( CONS (CONS NULL 9 NULL ) 1 NULL).
Definition C := CONS ( CONS NULL 3 NULL) 5 (NULL ).

Print A.
Print B.
Print C.


(*EX 2*)
Fixpoint Size {T : Type} (X : ArboreB T) : nat :=
  match X with
  | NULL => 0
  | CONS stanga x dreapta => 1 + Size stanga + Size dreapta
 end.

Compute Size A.
Compute Size B.

(*EX 3*)
Fixpoint Height {T : Type} (X : ArboreB T) : nat :=
  match X with
  | NULL => 0
  | CONS stanga R dreapta => 1 + max (Height stanga) (Height dreapta)
  end.

Compute Height A.
Compute Height B.

(*EX 5*)
(* Funcția flatten *)
Fixpoint flatten {T : Type} (tree : ArboreB T) (f : T -> T) : list T :=
  match tree with
  | NULL => []
  | CONS stanga x dreapta =>
    f x :: (flatten stanga f) ++ (flatten dreapta f)
  end.

Definition EX (x : nat) : nat :=
  x * 2.

Compute flatten B EX.







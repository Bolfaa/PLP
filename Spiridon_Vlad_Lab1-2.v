Inductive Day := 
    | Luni
    | Marti
    | Miercuri
    | Joi
    | Vineri
    | Sambata
    | Duminica.

Check Joi.
(*EX3*)
Definition Next (d : Day) : Day := 
    match d with
    | Luni => Marti
    | Marti => Miercuri
    | Miercuri => Joi
    | Joi => Vineri
    | Vineri => Sambata
    | Sambata => Duminica
    | Duminica => Luni
end.

Check Next.

Compute (Next Duminica).
Compute (Next Luni).
Compute (Next Joi).

(*EX4*)
Inductive boolean :=
    | T
    | F.

Check F.
(*FUNCTII PE BOOL*)
Definition nu ( d : boolean ) :boolean := 
    match d with
    | T => F 
    | F => T    
end.

Compute nu T.
Compute nu F.

Definition si(d1 d2 : boolean ) :boolean := 
    match d1 , d2 with
    | T , T => T  
    | T , F => F
    | F , F => F
    | F , T => F
end.

Compute si T T.
Compute si F T.
Compute si F F.

Definition sau (d1 d2 : boolean ) :boolean := 
    match d1 , d2 with
    | T , T => T  
    | T , F => T
    | F , F => F
    | F , T => T
end.

Compute sau T T.
Compute sau F T.
Compute sau F F.
(*Compute sau T (sau F).*)


Inductive Byte :=
| c: boolean -> boolean -> boolean -> boolean -> boolean -> boolean -> boolean -> boolean -> Byte.

Check c T F F T F T F T.

Inductive Pair := pair : boolean -> boolean ->Pair.

Definition add3 (b1 b2 cr : boolean): Pair :=
match b1,b2,cr with
| T,T,T => pair T T
| T,T,F => pair T F
| T,F,F => pair F T
| F,F,F => pair F F
| F,T,T => pair T F
| F,T,F => pair F T
| F,F,T => pair F T
| T,F,T => pair T F
end.

Definition scad3 (b1 b2 cr : boolean): Pair :=
match b1,b2,cr with
| T,T,T => pair T F
| T,T,F => pair F F
| T,F,F => pair F T
| F,F,F => pair F F
| F,T,T => pair F F
| F,T,F => pair F T
| F,F,T => pair T F
| T,F,T => pair F T
end.

Definition add ( n m :Byte ) :Byte :=
match n, m with 
| c i7 i6 i5 i4 i3 i2 i1 i0, c j7 j6 j5 j4 j3 j2 j1 j0 =>
let ( cr0 , r0) := add3 i0 j0 F in
let ( cr1 , r1) := add3 i1 j1 cr0 in
let ( cr2 , r2) := add3 i2 j2 cr1 in
let ( cr3 , r3) := add3 i3 j3 cr2 in
let ( cr4 , r4) := add3 i4 j4 cr3 in
let ( cr5 , r5) := add3 i5 j5 cr4 in
let ( cr6 , r6) := add3 i6 j6 cr5 in
let ( cr7 , r7) := add3 i7 j7 cr6 in
(c r7 r6 r5 r4 r3 r2 r1 r0)
end.

Compute add (c F F F F F F F T ) (c F F F F F F F T).





Require Import Strings.String.
Require Import Coq.ZArith.BinInt.
Local Open Scope string_scope. 
Local Open Scope list_scope.
Local Open Scope Z_scope.
Scheme Equality for string.

Inductive newString : Type :=
| errString : newString
| stringVal : string -> newString.

Inductive newNat : Type :=
| errNat : newNat
| natVal : nat -> newNat.

Inductive newInt : Type :=
| errInt : newInt
| intVal : Z -> newInt.

Inductive newBool : Type :=
| errBool : newBool
| boolVal : bool -> newBool.

Inductive newPointer : Type :=
| NULL : newPointer
| pointerVal : nat -> newPointer.

Notation "'str(' S ')'" := (stringVal S) (at level 0).
Coercion intVal : Z >-> newInt.
Coercion natVal : nat >-> newNat.
Coercion boolVal : bool >-> newBool.
Coercion pointerVal : nat >-> newPointer.

Inductive newType : Type :=
| err_undeclared : newType
| err_assignment : newType
| default : newType
| natType : newNat -> newType
| intType : newInt -> newType
| boolType : newBool -> newType
| stringType : newString -> newType
| pointType : newPointer -> newType.

Inductive Exp:=
| n_const : newNat -> Exp
| i_const : newInt -> Exp
| b_const : newBool -> Exp
| avar : string -> Exp
| adunare : Exp -> Exp -> Exp
| scadere : Exp -> Exp -> Exp
| inmultire : Exp -> Exp -> Exp
| impartire : Exp -> Exp -> Exp
| modulo : Exp -> Exp -> Exp
| putere : Exp -> Exp -> Exp
| negatie : Exp -> Exp
| si_logic : Exp -> Exp -> Exp
| sau_logic : Exp -> Exp -> Exp
| mai_mic : Exp -> Exp -> Exp
| mai_micEq : Exp -> Exp -> Exp
| mai_mare : Exp-> Exp -> Exp
| mai_mareEq : Exp -> Exp -> Exp
| egalitate : Exp -> Exp -> Exp
| inegalitate : Exp -> Exp -> Exp
| sau_exclusiv : Exp -> Exp -> Exp
| si_exclusiv: Exp -> Exp -> Exp.

Coercion n_const : newNat >-> Exp.
Coercion i_const : newInt >-> Exp.
Coercion b_const : newBool >-> Exp.
Coercion avar : string >-> Exp.

(*Notatii expresii algebrice*)
Notation "A +' B" := (adunare A B)(at level 50, left associativity).
Notation "A -' B" := (scadere A B)(at level 50, left associativity).
Notation "A *' B" := (inmultire A B)(at level 48, left associativity).
Notation "A /' B" := (impartire A B)(at level 48, left associativity).
Notation "A %' B" := (modulo A B)(at level 48, left associativity).
Notation "A ^' B" := (putere A B) (at level 48, left associativity).

(*Notatii expresii booleene*)
Notation "!' A" := (negatie A) (at level 45, right associativity).
Notation "A &&' B" := (si_logic A B) (at level 55, left associativity).
Notation "A 'xand' B" := (si_exclusiv A B) (at level 55, left associativity).
Notation "A ||' B" := (si_logic A B) (at level 56, left associativity).
Notation "A 'xor' B" := (sau_exclusiv A B) (at level 56, left associativity).
Notation "A <=' B" := (mai_micEq A B) (at level 52, left associativity).
Notation "A <' B" := (mai_mic A B) (at level 52, left associativity).
Notation "A >=' B" := (mai_micEq A B) (at level 52, left associativity).
Notation "A >' B" := (mai_mic A B) (at level 52, left associativity).
Notation "A ==' B" := (egalitate A B) (at level 53, left associativity).
Notation "A !=' B" := (egalitate A B) (at level 53, left associativity).







Require Import Strings.String.
Require Import Coq.ZArith.BinInt.
Require Import Coq.Lists.List.
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

Notation "'str(' S ')'" := (stringVal S) (at level 0).
Coercion intVal : Z >-> newInt.
Coercion natVal : nat >-> newNat.
Coercion boolVal : bool >-> newBool.

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

(*Operatii pe stringuri*)
Inductive SExp :=
| s_const : newString -> SExp
| s_concat : newString -> newString -> SExp
| s_toNat : newString -> SExp.

Coercion s_const : newString >-> SExp.
Notation "'concat(' S1 , S2 ')'" := (s_concat S1 S2) (at level 50, left associativity).
Notation "'strToNat(' S ')'" := (s_toNat S) (at level 0).

(*inafara functiilor se pot declara variabile
 doar cu valoarea default*)
Inductive Lang :=
| secvLang : Lang -> Lang -> Lang
| decl_nat0 : string -> Lang
| decl_int0 : string -> Lang
| decl_bool0 : string -> Lang
| decl_string0 : string -> Lang
| functiaMain : Stmt -> Lang
| functie : string -> list string -> Stmt -> Lang
(*in interiorul unei functii se pot declara 
variabile doar cu o valoare introdusa manual*)
with Stmt := 
| decl_nat : string -> Exp -> Stmt
| decl_int : string -> Exp -> Stmt
| decl_bool : string -> Exp -> Stmt
| decl_string : string -> SExp -> Stmt
| skip : Stmt
| secventa : Stmt -> Stmt -> Stmt
| break : Stmt
| continue : Stmt
| asignare : string -> Exp -> Stmt
| str_asig : string -> SExp -> Stmt
| ifthen : Exp -> Stmt -> Stmt
| ifthenelse : Exp -> Stmt -> Stmt -> Stmt
| whileloop : Exp -> Stmt -> Stmt
| dowhile : Stmt -> Exp -> Stmt
| forloop : Stmt -> Exp -> Stmt -> Stmt -> Stmt
| switch : Exp -> list Cases -> Stmt
| citeste : string -> Stmt
| scrie : newString -> Stmt
with Cases :=
| caseDefault : Stmt -> Cases
| caseOther : Exp -> Stmt -> Cases.

Print list.

Inductive newType : Type :=
| err_undeclared : newType
| err_assignment : newType
| default : newType
| natType : newNat -> newType
| intType : newInt -> newType
| boolType : newBool -> newType
| stringType : newString -> newType.

Notation "'uint0'' V" := (decl_nat0 V) (at level 90, right associativity).
Notation "'uint'' V <-- E" := (decl_nat V E) (at level 90, right associativity).

Notation "'int0'' V" := (decl_int0 V) (at level 90, right associativity).
Notation "'int'' V <-- E" := (decl_int V E) (at level 90, right associativity).

Notation "'bool0'' V" := (decl_bool0 V) (at level 90, right associativity).
Notation "'bool'' V <-- E" := (decl_bool V E) (at level 90, right associativity).

Notation "'string0'' V" := (decl_string0 V) (at level 90, right associativity).
Notation "'string'' V <-- E" := (decl_string V E) (at level 90, right associativity).

Notation "V ::= E" := (asignare V E) (at level 90, right associativity).
Notation "S :s= E" := (str_asig S E) (at level 90, right associativity).

Notation "S1 ;; S2" := (secventa S1 S2) (at level 93, right associativity).
Notation "S1 ;' S2" := (secvLang S1 S2) (at level 93, right associativity).

Notation "'if'' ( B ) 'then'' { S } 'end''" := (ifthen B S) (at level 97).
Notation "'if'' ( B ) 'then'' { S1 } 'else'' '{' S2 '}' 'end''" := (ifthenelse B S1 S2) (at level 97).

Notation "'while'' ( B ) 'do'' { S } 'end''" := (whileloop B S) (at level 97).
Notation "'do'' { S } 'while'' ( B ) 'end''" := (dowhile S B) (at level 97).
Notation "'for'' ( I # B # A ) 'do'' { S } 'end''" := (forloop I B A S) (at level 97).

Notation "'default' : { S }" := (caseDefault S) (at level 96).
Notation "'case' ( E ):{ S }" := (caseOther E S) (at level 96).
Notation "'switch'' ( E ){ C1 } 'end''" := (switch E (cons C1 nil)) (at level 97).
Notation "'switch'' ( E ){ C1 C2 .. Cn  } 'end''" := (switch E (cons C1 (cons C2 .. (cons Cn nil) ..))) (at level 97).


Notation "'func' 'main' (()){} 'end''" := (functiaMain skip)(at level 95).
Notation "'func' 'main' (()){ S } 'end''" := (functiaMain S)(at level 95). 

Notation "'func' N (()){} 'end''" := (functie N nil skip)(at level 95).
Notation "'func' N (()){ S } 'end''" := (functie N nil S)(at level 95).
Notation "'func' N (( A )){} 'end''" := (functie N (cons A nil) skip)(at level 95).

Notation "'write(' S )" := (scrie S) (at level 92).
Notation "'read(' V )" := (citeste V) (at level 92).

Check func "mama"(("a")){} end'.






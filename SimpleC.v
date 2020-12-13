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

Notation "'str(' S )" := (stringVal S) (at level 0).
Coercion intVal : Z >-> newInt.
Coercion natVal : nat >-> newNat.
Coercion boolVal : bool >-> newBool.

Inductive Exp:=
| n_const : newNat -> Exp (*constanta de tip nat*)
| i_const : newInt -> Exp (*constanta de tip int*)
| b_const : newBool -> Exp (*constanta de tip bool*)
| avar : string -> Exp (*variabila de tip nat/int/bool*)
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
| si_exclusiv: Exp -> Exp -> Exp
(*operatii pe string-uri*)
| s_const : newString -> Exp (*constanta de tip string*)
| s_concat : newString -> newString -> Exp (*concateneaza doua string-uri*)
| s_toNat : newString -> Exp (*transforma un string in numar natural*)
| s_toInt : newString -> Exp. (*transforma un string in numar intreg*)

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

Coercion s_const : newString >-> Exp.
Notation "'concat(' S1 , S2 ')'" := (s_concat S1 S2) (at level 50, left associativity).
Notation "'strToNat(' S ')'" := (s_toNat S) (at level 0).

(*inafara functiilor se pot declara variabile
 doar cu valoarea default*)
Inductive Lang :=
| secvLang : Lang -> Lang -> Lang (*secventa de Lang*)
| decl_nat0 : string -> Lang (*declarare nat cu valoare default*)
| decl_int0 : string -> Lang  (*declarare int cu valoare default*)
| decl_bool0 : string -> Lang (*declarare bool cu valoare default*)
| decl_string0 : string -> Lang(*declarare string cu valoare default*)
| functiaMain : Stmt -> Lang  (*functia principala main*)
| functie : string -> list string -> Stmt -> Lang (*declarare de functii*)
(*in interiorul unei functii se pot declara 
variabile doar cu o valoare introdusa manual*)
with Stmt := 
 decl_nat : string -> Exp -> Stmt (*declarare nat cu o valoare specificata*)
| decl_int : string -> Exp -> Stmt (*declarare int cu o valoare specificata*)
| decl_bool : string -> Exp -> Stmt (*declarare bool cu o valoare specificata*)
| decl_string : string -> Exp -> Stmt (*declarare string cu o valoare specificata*)
| secventa : Stmt -> Stmt -> Stmt (*secventa de Stmt*)
| skip : Stmt (*bloc gol e instructiuni*)
| break : Stmt (*iesi din loop*)
| continue : Stmt (*treci direct la urmatoarea iteratie*)
| asignare : string -> Exp -> Stmt (*asigneaza o valoare unei variabile*)
| citeste : string -> Stmt (*citeste inputul si il pune intr-o variabila*)
| scrie : newString -> Stmt (*scrie un string*)
| ifthen : Exp -> Stmt -> Stmt (*if cu o singura ramura*)
| ifthenelse : Exp -> Stmt -> Stmt -> Stmt (*if cu doua ramuri*)
| whileloop : Exp -> Stmt -> Stmt (*instructiunea repetitiva while*)
| dowhile : Stmt -> Exp -> Stmt (*instructiunea repetitiva do-while*)
| forloop : Stmt -> Exp -> Stmt -> Stmt -> Stmt (*instructiunea repetitiva for*)
| switch : Exp -> list Cases -> Stmt (*swtch() cu unul sau mai multe cazuri*)
(*tip nou pentru case-urile din switch*)
with Cases :=
 caseDefault : Stmt -> Cases (*cazul implicit al switch-ului*)
| caseOther : Exp -> Stmt -> Cases. (*alte cazuri*)

Print list.

Inductive newType : Type :=
| err_undeclared : newType (*eroare variabile nedeclarata*)
| err_assignment : newType (*eroare asignare variabila nedeclarata*)
| default : newType (*variabila contine valoarea default*)
| natType : newNat -> newType (*variabila este de tip nat*)
| intType : newInt -> newType (*variabila este de tip int*)
| boolType : newBool -> newType (*variabila este de tip bool*)
| stringType : newString -> newType. (*variabila este de tip string*)

Notation "'uint0'' V" := (decl_nat0 V) (at level 90, right associativity).
Notation "'uint'' V <-- E" := (decl_nat V E) (at level 90, right associativity).

Notation "'int0'' V" := (decl_int0 V) (at level 90, right associativity).
Notation "'int'' V <-- E" := (decl_int V E) (at level 90, right associativity).

Notation "'bool0'' V" := (decl_bool0 V) (at level 90, right associativity).
Notation "'bool'' V <-- E" := (decl_bool V E) (at level 90, right associativity).

Notation "'string0'' V" := (decl_string0 V) (at level 90, right associativity).
Notation "'string'' V <-- E" := (decl_string V E) (at level 90, right associativity).

Notation "V ::= E" := (asignare V E) (at level 90, right associativity).

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





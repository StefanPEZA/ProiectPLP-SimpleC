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

(*operatii pe string-uri*)
Inductive SExp :=
| s_const : newString -> SExp (*constanta de tip string*)
| svar : string -> SExp (*variabila de tip string*)
| s_concat : newString -> newString -> SExp (*concateneaza doua string-uri*)
| toString : string -> SExp. (*transorma orice variabila intr-un string*)

Inductive AExp:=
| i_const : newInt -> AExp (*constanta de tip int*)
| n_const : newNat -> AExp (*constanta de tip nat*)
| avar : string -> AExp (*variabila de tip nat/int*)
| adunare : AExp -> AExp -> AExp
| scadere : AExp -> AExp -> AExp
| inmultire : AExp -> AExp -> AExp
| impartire : AExp -> AExp -> AExp
| modulo : AExp -> AExp -> AExp
| putere : AExp -> AExp -> AExp
| toNat : string -> AExp (*transforma orice intr-un numar natural*)
| toInt : string -> AExp (*transforma orice intr-un intreg*)
| strLen : SExp -> AExp.

Inductive BExp :=
| b_const : newBool -> BExp (*constanta de tip bool*)
| bvar : string -> BExp (*variabila de tipul bool*)
| negatie : BExp -> BExp
| si_logic : BExp -> BExp -> BExp
| sau_logic : BExp -> BExp -> BExp
| mai_mic : AExp -> AExp -> BExp
| mai_micEq : AExp -> AExp -> BExp
| mai_mare : AExp-> AExp -> BExp
| mai_mareEq : AExp -> AExp -> BExp
| egalitate : AExp -> AExp -> BExp
| inegalitate : AExp -> AExp -> BExp
| sau_exclusiv : BExp -> BExp -> BExp
| si_exclusiv: BExp -> BExp -> BExp
| toBool : string -> BExp. (*transforma un numar in boolean*)

Coercion i_const : newInt >-> AExp.
Coercion n_const : newNat >-> AExp.
Coercion b_const : newBool >-> BExp.
Coercion s_const : newString >-> SExp.
Coercion avar : string >-> AExp.
Coercion bvar : string >-> BExp.
Coercion svar : string >-> SExp.

Notation "'Concat(' S1 , S2 )" := (concat S1 S2) (at level 50, left associativity).
Notation "'ToNat(' S )" := (toNat S) (at level 0).
Notation "'ToInt(' S )" := (toInt S) (at level 0).
Notation "'ToBool(' S )" := (toBool S) (at level 0).
Notation "'ToString(' S )" := (toString S) (at level 0).
Notation "'StrLen(' S )" := (strLen S) (at level 0).

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

Inductive Stmt := 
(*in interiorul unei functii se pot declara 
variabile doar cu o valoare introdusa manual*)
| decl_nat : string -> AExp -> Stmt (*declarare nat cu o valoare specificata*)
| decl_int : string -> AExp -> Stmt (*declarare int cu o valoare specificata*)
| decl_bool : string -> BExp -> Stmt (*declarare bool cu o valoare specificata*)
| decl_string : string -> SExp -> Stmt (*declarare string cu o valoare specificata*)
| secventa : Stmt -> Stmt -> Stmt (*secventa de Stmt*)
| skip : Stmt (*bloc gol e instructiuni*)
| break : Stmt (*iesi din loop*)
| continue : Stmt (*treci direct la urmatoarea iteratie*)
| asig_nr : string -> AExp -> Stmt (*asigneaza o valoare unei variabile de tip numar*)
| asig_bool : string -> BExp -> Stmt (*asigneaza o valoare unei variabile de tip bool*)
| asig_str : string -> SExp -> Stmt (*asigneaza o valoare unei variabile de tip string*)
| citeste : string -> Stmt (*citeste inputul si il pune intr-o variabila*)
| scrie : SExp -> Stmt (*scrie un string*)
| ifthen : BExp -> Stmt -> Stmt (*if cu o singura ramura*)
| ifthenelse : BExp -> Stmt -> Stmt -> Stmt (*if cu doua ramuri*)
| whileloop : BExp -> Stmt -> Stmt (*instructiunea repetitiva while*)
| dowhile : Stmt -> BExp -> Stmt (*instructiunea repetitiva do-while*)
| forloop : Stmt -> BExp -> Stmt -> Stmt -> Stmt (*instructiunea repetitiva for*)
| switch : AExp -> list Cases -> Stmt (*swtch() cu unul sau mai multe cazuri*)
| apelfunc : string -> list string -> Stmt (*apelul unei functii*)
(*tip nou pentru case-urile din switch*)
with Cases :=
 caseDefault : Stmt -> Cases (*cazul implicit al switch-ului*)
| caseOther : AExp -> Stmt -> Cases. (*alte cazuri*)

Inductive newType : Type :=
| err_undeclared : newType (*eroare variabile nedeclarata*)
| err_assignment : newType (*eroare asignare variabila nedeclarata*)
| default : newType (*variabila contine valoarea default*)
| natType : newNat -> newType (*variabila este de tip nat*)
| intType : newInt -> newType (*variabila este de tip int*)
| boolType : newBool -> newType (*variabila este de tip bool*)
| stringType : newString -> newType (*variabila este de tip string*)
| code : Stmt -> newType. (*codul unei funcii*)

Coercion code : Stmt >-> newType.

(*inafara functiilor se pot declara variabile
 doar cu valoarea default*)
Inductive Lang :=
| secvLang : Lang -> Lang -> Lang (*secventa de Lang*)
| decl_nat0 : string -> Lang (*declarare nat cu valoare default*)
| decl_int0 : string -> Lang  (*declarare int cu valoare default*)
| decl_bool0 : string -> Lang (*declarare bool cu valoare default*)
| decl_string0 : string -> Lang(*declarare string cu valoare default*)
| functiaMain : Stmt -> Lang  (*functia principala main*)
| functie : string -> list string -> Stmt -> Lang. (*declarare de functii*)

Notation "'uint0'' V" := (decl_nat0 V) (at level 90, right associativity).
Notation "'uint'' V <-- E" := (decl_nat V E) (at level 90, right associativity).

Notation "'int0'' V" := (decl_int0 V) (at level 90, right associativity).
Notation "'int'' V <-- E" := (decl_int V E) (at level 90, right associativity).

Notation "'bool0'' V" := (decl_bool0 V) (at level 90, right associativity).
Notation "'bool'' V <-- E" := (decl_bool V E) (at level 90, right associativity).

Notation "'string0'' V" := (decl_string0 V) (at level 90, right associativity).
Notation "'string'' V <-- E" := (decl_string V E) (at level 90, right associativity).

Notation "V :N= E" := (asig_nr V E) (at level 90, right associativity).
Notation "V :B= E" := (asig_bool V E) (at level 90, right associativity).
Notation "V :S= E" := (asig_str V E) (at level 90, right associativity).

Notation "S1 ;; S2" := (secventa S1 S2) (at level 93, right associativity).
Notation "S1 ;' S2" := (secvLang S1 S2) (at level 93, right associativity).

Notation "'if'(' B ) 'then'{' S '}end'" := (ifthen B S) (at level 97).
Notation "'if'(' B ) 'then'{' S1 '}else'{' S2 '}end'" := (ifthenelse B S1 S2) (at level 97).

Notation "'while'(' B ) 'do'{' S }" := (whileloop B S) (at level 97).
Notation "'do'{' S '}while(' B )" := (dowhile S B) (at level 97).
Notation "'for'(' I ; B ; A ) 'do'{' S }" := (forloop I B A S) (at level 97).

Notation "'default:{' S };" := (caseDefault S) (at level 96).
Notation "'case(' E ):{ S };" := (caseOther E S) (at level 96).
Notation "'switch'(' E ){ C1 .. Cn '}end'" := (switch E (cons C1 .. (cons Cn nil) .. )) (at level 97).

Notation "'void' 'main()' { }" := (functiaMain skip)(at level 95).
Notation "'void' 'main()' { S }" := (functiaMain S)(at level 95). 

Notation "'void' N (){ }" := (functie N nil skip)(at level 95).
Notation "'void' N (){ S }" := (functie N nil S)(at level 95).
Notation "'void' N (( A1 , .. , An )){ }" := (functie N (cons A1 .. (cons An nil) .. ) skip)(at level 95).
Notation "'void' N (( A1 , .. , An )){ S }" := (functie N (cons A1 .. (cons An nil) .. ) S)(at level 95).

Notation "'call' N (( A1 , .. , An ))" := (apelfunc N (cons A1 .. (cons An nil) .. ) ) (at level 89).
Notation "'call' N (( ))" := (apelfunc N nil) (at level 89).

Notation "'write(' S )" := (scrie S) (at level 92).
Notation "'read(' V )" := (citeste V) (at level 92).

(*secveta de cod (sintaxa)*)
Check
  void "nothing" (){ } ;'
  uint0' "nr_nat" ;'
  void "scrie" (("string")){
     write( "string" )
  } ;'
  bool0' "bool" ;'
  string0' "str" ;'
  int0' "nr_intreg" ;'
  void main(){
     int' "n" <-- -1 ;;
     bool' "ok" <-- ("n" !=' 0) ;;
     if'("ok") then'{
        "n" :N= 0
     }end ;;
     while'(true) do'{
        if'("n" >' 2) then'{
          string' "str" <-- str("numarul mai mare decat 2") ;;
          break
        }else'{ "n" :N= "n" +' 1 }end
     } ;;
     write("str")
  }.





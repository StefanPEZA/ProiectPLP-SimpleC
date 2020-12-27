Require Import Strings.String.
Require Import Coq.ZArith.BinInt.
Require Import Coq.Lists.List.
Local Open Scope string_scope. 
Local Open Scope list_scope.
Local Open Scope N_scope.
Local Open Scope Z_scope.

Inductive Var :=
|Id : string -> Var.
Coercion Id : string >-> Var.
Scheme Equality for Var.

Inductive newString : Type :=
| errString : newString
| strVal : string -> newString.

Inductive newNr : Type :=
| errNr : newNr
| nrVal : Z -> newNr.

Inductive newBool : Type :=
| errBool : newBool
| boolVal : bool -> newBool.

Notation "'str(' S )" := (strVal S) (at level 0).
Coercion nrVal : Z >-> newNr.
Coercion boolVal : bool >-> newBool.

(*operatii pe string-uri*)
Inductive SExp :=
| sconst : newString -> SExp (*constanta de tip string*)
| svar : Var -> SExp (*variabila de tip string*)
| ref_str : Var -> SExp (*referinta catre un string*)
| sconcat : SExp -> SExp -> SExp (*concateneaza doua string-uri*)
| toString : Var -> SExp. (*transorma orice variabila intr-un string*)

(*funtia de concatenare a doua string-uri*)
Definition fun_strConcat (s1 s2: newString) : newString :=
match s1 , s2 with 
  |errString, _ => errString
  |_, errString => errString
  |strVal str1, strVal str2 => strVal (str1 ++ str2)
end.

Fixpoint Length_help (s : string) : Z :=
  match s with
  | EmptyString => Z0
  | String c s' => 1 + Length_help s'
  end.

Definition fun_strlen (s : newString) : newNr :=
match s with 
| errString => errNr
| strVal str1 => nrVal (Length_help str1)
end.


Inductive AExp:=
| aconst : newNr -> AExp (*constanta de tip int*)
| avar : Var -> AExp (*variabila de tip nat/int*)
| ref_nat : Var -> AExp (*referinta la catre un nat*)
| ref_int : Var -> AExp (*referinta la catre un int*)
| adunare : AExp -> AExp -> AExp
| scadere : AExp -> AExp -> AExp
| inmultire : AExp -> AExp -> AExp
| impartire : AExp -> AExp -> AExp
| modulo : AExp -> AExp -> AExp
| putere : AExp -> AExp -> AExp
| toNr : BExp -> AExp (*transforma un bool intr-un numar*)
| strLen : SExp -> AExp (* returneaza lungimea unui string*)
with BExp :=
| bconst : newBool -> BExp (*constanta de tip bool*)
| bvar : Var -> BExp (*variabila de tipul bool*)
| ref_bool : Var -> BExp (*referinta catre un bool*)
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
| toBool : AExp -> BExp. (*transforma un numar in boolean*)

Coercion aconst : newNr >-> AExp.
Coercion bconst : newBool >-> BExp.
Coercion sconst : newString >-> SExp.
Coercion avar : Var >-> AExp.
Coercion bvar : Var >-> BExp.
Coercion svar : Var >-> SExp.

Notation "'Concat(' S1 , S2 )" := (sconcat S1 S2) (at level 50, left associativity).
Notation "'ToNr(' S )" := (toNr S) (at level 0).
Notation "'ToBool(' S )" := (toBool S) (at level 0).
Notation "'ToString(' S )" := (toString S) (at level 0).
Notation "'StrLen(' S )" := (strLen S) (at level 0).
Notation "'s*' V" := (ref_str V) (at level 0).

(*Notatii expresii algebrice*)
Notation "A +' B" := (adunare A B)(at level 50, left associativity).
Notation "A -' B" := (scadere A B)(at level 50, left associativity).
Notation "A *' B" := (inmultire A B)(at level 48, left associativity).
Notation "A /' B" := (impartire A B)(at level 48, left associativity).
Notation "A %' B" := (modulo A B)(at level 48, left associativity).
Notation "A ^' B" := (putere A B) (at level 48, left associativity).
Notation "'u*' V" := (ref_nat V) (at level 0).
Notation "'i*' V" := (ref_nat V) (at level 0).
 
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
Notation "'b*' V" := (ref_bool V) (at level 0).

Inductive Stmt := 
(*in interiorul unei functii se pot declara 
variabile doar cu o valoare introdusa manual*)
| point_int : Var -> Var -> Stmt
| point_bool : Var -> Var -> Stmt
| point_str : Var -> Var -> Stmt
| refasig_int : Var -> AExp -> Stmt
| refasig_bool : Var -> BExp -> Stmt
| refasig_str : Var -> SExp -> Stmt
| decl_int : Var -> AExp -> Stmt (*declarare int cu o valoare specificata*)
| decl_bool : Var -> BExp -> Stmt (*declarare bool cu o valoare specificata*)
| decl_string : Var -> SExp -> Stmt (*declarare string cu o valoare specificata*)
| secventa : Stmt -> Stmt -> Stmt (*secventa de Stmt*)
| skip : Stmt (*bloc gol e instructiuni*)
| break : Stmt (*iesi din loop*)
| continue : Stmt (*treci direct la urmatoarea iteratie*)
| asig_nr : Var -> AExp -> Stmt (*asigneaza o valoare unei variabile de tip numar*)
| asig_bool : Var -> BExp -> Stmt (*asigneaza o valoare unei variabile de tip bool*)
| asig_str : Var -> SExp -> Stmt (*asigneaza o valoare unei variabile de tip string*)
| citeste : Var -> Stmt (*citeste inputul si il pune intr-o variabila*)
| scrie : SExp -> Stmt (*scrie un string*)
| ifthen : BExp -> Stmt -> Stmt (*if cu o singura ramura*)
| ifthenelse : BExp -> Stmt -> Stmt -> Stmt (*if cu doua ramuri*)
| whileloop : BExp -> Stmt -> Stmt (*instructiunea repetitiva while*)
| dowhile : Stmt -> BExp -> Stmt (*instructiunea repetitiva do-while*)
| forloop : Stmt -> BExp -> Stmt -> Stmt -> Stmt (*instructiunea repetitiva for*)
| switch : AExp -> list Cases -> Stmt (*swtch() cu unul sau mai multe cazuri*)
| apelfunc : Var -> list Var -> Stmt (*apelul unei functii*)
(*tip nou pentru case-urile din switch*)
with Cases :=
 caseDefault : Stmt -> Cases (*cazul implicit al switch-ului*)
| caseOther : AExp -> Stmt -> Cases. (*alte cazuri*)

(*inafara functiilor se pot declara variabile
 doar cu valoarea default*)
Inductive Lang :=
| secvLang : Lang -> Lang -> Lang (*secventa de Lang*)
| decl_int0 : Var -> Lang  (*declarare int cu valoare default*)
| decl_bool0 : Var -> Lang (*declarare bool cu valoare default*)
| decl_string0 : Var -> Lang(*declarare string cu valoare default*)
| functiaMain : Stmt -> Lang  (*functia principala main*)
| functie : Var -> list Var -> Stmt -> Lang. (*declarare de functii*)

Inductive newType : Type :=
| error : newType (*tip de eroare*)
| nrType : newNr -> newType (*variabila este de tip numar*)
| boolType : newBool -> newType (*variabila este de tip bool*)
| strType : newString -> newType (*variabila este de tip string*)
| code : Stmt -> newType. (*codul unei funcii*)

Coercion code : Stmt >-> newType.

Notation "'int**' V <-- P" := (point_int V P) (at level 90).
Notation "'bool**' V <-- P" := (point_bool V P) (at level 90).
Notation "'string**' V <-- P" := (point_str V P) (at level 90).

Notation "'n*' V ::= E" := (refasig_int V E) (at level 90).
Notation "'b*' V ::= E" := (refasig_bool V E) (at level 90).
Notation "'s*' V ::= E":= (refasig_str V E) (at level 90).

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
Notation "'void' N (( A1 , .. , An )){ }" := (functie N (cons (Id A1) .. (cons (Id An) nil) .. ) skip)(at level 95).
Notation "'void' N (( A1 , .. , An )){ S }" := (functie N (cons (Id A1) .. (cons (Id An) nil) .. ) S)(at level 95).

Notation "'call' N (( A1 , .. , An ))" := (apelfunc N (cons (Id A1) .. (cons (Id An) nil) .. ) ) (at level 89).
Notation "'call' N (( ))" := (apelfunc N nil) (at level 89).

Notation "'write(' S )" := (scrie S) (at level 92).
Notation "'read(' V )" := (citeste V) (at level 92).

(*secventa de cod cu pointeri*)
Check (int** "to_int" <-- "nr2" ;;
       bool** "to_bool" <-- "ok" ;;
       string** "to_str" <-- "msg" ;;
       n* "to_int" ::= -5 ;;
       b* "to_bool" ::= true ;;
       s* "to_str" ::= str("mesaj !") ;;
       
       bool' "new" <-- false ;;
       "new" :B= true &&' b* "to_bool"
      ).

(*secveta de cod (sintaxa)*)
Check
  void "nothing" (){ } ;'
  void "scrie" (("string")){
     write( "string" )
  } ;'
  bool0' "bool" ;'
  string0' "str" ;'
  int0' "nr_intreg" ;'
  void main(){
     int' "n" <-- -1 ;;
     bool' "ok" <-- ("n" !=' 0) ;;
     if'("ok" &&' "n" <=' 0) then'{
        "n" :N= 0
     }end ;;
     while'(true) do'{
        if'("n" >' 2) then'{
          string' "str" <-- str("numarul mai mare decat 2") ;;
          break
        }else'{ "n" :N= "n" +' 1 }end
     } ;;
     call "scrie"(("str")) ;;
     switch'("a"){ default:{ skip }; }end
  }.


Definition Memory := nat -> newType.
Definition State := Var -> nat.
Inductive MemoryLayer := 
| pair : State -> Memory -> nat -> MemoryLayer.
Notation "<< S , M , N >>" := (pair S M N) (at level 0).

Definition getVal (m : MemoryLayer) (v : Var) : newType :=
match m with
| pair st mem _ => mem (st v)
end.

Definition getMaxPos (m : MemoryLayer) : nat :=
match m with
| pair _ _ max => max
end.

Definition getAdress (m:MemoryLayer) (v : Var) : nat :=
match m with
| pair state _ _ => state v
end.

Definition updateState (st : State) (v : Var) (n : nat) : State:= 
fun x => if (Var_beq x v) then n else st x.

Definition updateMemory (mem : Memory) (n : nat) (val : newType) : Memory :=
fun n' => if (Nat.eqb n' n) then val else mem n'. 

Definition update (M : MemoryLayer) (V : Var) (T : newType) (pos : nat) : MemoryLayer :=
match M with
|<<st, mem, max>> => if (andb (Nat.eqb pos (getAdress M V) ) (Nat.eqb pos 0) ) then
       <<st, mem, max>> else
       <<updateState st V pos, updateMemory mem pos T, 
      (if (Nat.ltb pos max) then max else Nat.add max 1) >>
end.
 
Definition mem0 : Memory := fun n => error.
Definition state0 : State := fun x => 0%nat.
Definition stack0 := <<state0, mem0, 1>>.

Definition newPlus (a b : newType) :=
match a, b with
| nrType a', nrType b' => match a', b' with
                        | nrVal n1, nrVal n2 => nrType (n1 + n2)
                        | _, _ => nrType errNr
                        end
| _ , _ => error
end.

Definition newMinus (a b : newType) :=
match a, b with
| nrType a', nrType b' => match a', b' with
                        | nrVal n1, nrVal n2 => nrType (n1 - n2)
                        | _, _ => nrType errNr
                        end
| _ , _ => error
end.

Definition newTimes (a b : newType) :=
match a, b with
| nrType a', nrType b' => match a', b' with
                        | nrVal n1, nrVal n2 => nrType (n1 * n2)
                        | _, _ => nrType errNr
                        end
| _ , _ => error
end.

Definition newDivide (a b : newType) :=
match a, b with
| nrType a', nrType b' => match a', b' with
                        | nrVal n1, nrVal n2 => if (Z.eqb n2 0) then nrType errNr else nrType (n1 / n2)
                        | _, _ => nrType errNr
                        end
| _ , _ => error
end.

Definition newModulo (a b : newType) :=
match a, b with
| nrType a', nrType b' => match a', b' with
                        | nrVal n1, nrVal n2 => if (Z.eqb n2 0) then nrType errNr else nrType (Z.modulo n1 n2)
                        | _, _ => nrType errNr
                        end
| _ , _ => error
end.

Definition newPower (a b : newType) :=
match a, b with
| nrType a', nrType b' => match a', b' with
                        | nrVal n1, nrVal n2 => if (Z.ltb n2 0) then nrType errNr else nrType (Z.pow n1 n2)
                        | _, _ => nrType errNr
                        end
| _ , _ => error
end.

Definition newStrlen (a : newType) :=
match a with
| strType a' => nrType ( fun_strlen a' )
| _ => error
end.

Definition newStrcat (s1 s2 : newType) := 
match s1, s2 with
| strType s1', strType s2' => strType ( fun_strConcat s1' s2' )
| _, _ => error
end.

Definition newToNr (a : newType) := 
match a with
|boolType a' => match a' with
                | errBool => nrType errNr
                | boolVal b => if (b) then (nrType 1) else (nrType 0)
                end
|_ => error
end.

Definition notb (a : bool) : bool :=
match a with
| true => false
| false => true
end.

Definition newComp (type : string) (a b : newType) : newType := 
match a, b with
| nrType a', nrType b' 
          => match a', b' with
          | nrVal a'', nrVal b'' 
                        => match type with
                           | "lt" => boolType (Z.ltb a'' b'')
                           | "le" => boolType (Z.leb a'' b'')
                           | "gt" => boolType (Z.ltb b'' a'')
                           | "ge" => boolType (Z.leb b'' a'')
                           | "eq" => boolType (Z.eqb a'' b'')
                           | _ => boolType (notb (Z.eqb a'' b'') )
                           end
          | _, _ => boolType errBool
          end
| _, _ => error
end.

Definition newOrB (a b : newType) : newType := 
match a, b with
| boolType a', boolType b' => match a', b' with
                              | boolVal a'', boolVal b'' => boolType (orb a'' b'')
                              | _, _ => boolType errBool
                              end
| _, _ => error
end.

Definition xorb (a b : bool) : bool :=
match a, b with 
| true, true => false
| false, false => false
| _, _ => true
end.

Definition newXor (a b : newType) : newType := 
match a, b with
| boolType a', boolType b' => match a', b' with
                              | boolVal a'', boolVal b'' => boolType (xorb a'' b'')
                              | _, _ => boolType errBool
                              end
| _, _ => error
end.

Definition newXand (a b : newType) : newType := 
match a, b with
| boolType a', boolType b' => match a', b' with
                              | boolVal a'', boolVal b'' => boolType ( notb (xorb a'' b'') )
                              | _, _ => boolType errBool
                              end
| _, _ => error
end.

Definition newToBool (a : newType) := 
match a with
|nrType a' => match a' with
                | errNr => nrType errNr
                | nrVal n => if (Z.eqb n 0) then (boolType false) else (boolType true)
                end
|_ => error
end.


Reserved Notation "STR '=S[' St ']S>' N" (at level 60).
Inductive seval : SExp -> MemoryLayer -> newType -> Prop :=
| s_const : forall s sigma, sconst s =S[ sigma ]S> strType s
| s_var : forall s sigma, svar s =S[ sigma ]S> getVal sigma s
| s_concat : forall s1 s2 sigma s st1 st2,
    s1 =S[ sigma ]S> st1 ->
    s2 =S[ sigma ]S> st2 ->
    s = newStrcat st1 st2 ->
    Concat( s1 , s2 ) =S[ sigma ]S> s
where "STR '=S[' St ']S>' N" := (seval STR St N).


Reserved Notation "B '=B[' S ']B>' B'" (at level 70).
Reserved Notation "A '=A[' S ']A>' N" (at level 60).
Inductive aeval : AExp -> MemoryLayer -> newType -> Prop :=
| e_const : forall n sigma, aconst n =A[ sigma ]A> nrType n
| e_var : forall v sigma, avar v =A[ sigma ]A> getVal sigma v
| e_add : forall a1 a2 i1 i2 sigma n,
    a1 =A[ sigma ]A> i1 ->
    a2 =A[ sigma ]A> i2 ->
    n = newPlus i1 i2 ->
    a1 +' a2 =A[ sigma ]A> n
| e_sub : forall a1 a2 i1 i2 sigma n,
    a1 =A[ sigma ]A> i1 ->
    a2 =A[ sigma ]A> i2 ->
    n = newMinus i1 i2 ->
    a1 -' a2 =A[ sigma ]A> n
| e_times : forall a1 a2 i1 i2 sigma n,
    a1 =A[ sigma ]A> i1 ->
    a2 =A[ sigma ]A> i2 ->
    n = newTimes i1 i2 ->
    a1 *' a2 =A[ sigma ]A> n
| e_divided : forall a1 a2 i1 i2 sigma n,
    a1 =A[ sigma ]A> i1 ->
    a2 =A[ sigma ]A> i2 ->
    n = newDivide i1 i2 ->
    a1 /' a2 =A[ sigma ]A> n
| e_div_rest : forall a1 a2 i1 i2 sigma n,
    a1 =A[ sigma ]A> i1 ->
    a2 =A[ sigma ]A> i2 ->
    n = newModulo i1 i2 ->
    a1 %' a2 =A[ sigma ]A> n
| e_power : forall a1 a2 i1 i2 sigma n,
    a1 =A[ sigma ]A> i1 ->
    a2 =A[ sigma ]A> i2 ->
    n = newPower i1 i2 ->
    a1 ^' a2 =A[ sigma ]A> n
| e_strlen : forall a1 sigma s1 n,
    a1 =S[ sigma ]S> s1 ->
    n = newStrlen s1 ->
    StrLen( a1 ) =A[ sigma ]A> n
| e_tonr : forall b1 sigma t1 a,
    b1 =B[ sigma ]B> t1 ->
    a = newToNr t1 ->
    ToNr( b1 ) =A[ sigma ]A> a
where "A '=A[' S ']A>' N" := (aeval A S N)
with beval : BExp -> MemoryLayer -> newType -> Prop :=
| e_true : forall sigma, true =B[ sigma ]B> boolType true
| e_false : forall sigma, false =B[ sigma ]B> boolType false
| e_bvar : forall v sigma, bvar v =B[ sigma ]B> getVal sigma v
| e_lessthan : forall a1 a2 i1 i2 sigma b,
    a1 =A[ sigma ]A> i1 ->
    a2 =A[ sigma ]A> i2 ->
    b = newComp "lt" i1 i2 ->
    a1 <' a2 =B[ sigma ]B> b
| e_lessthan_eq : forall a1 a2 i1 i2 sigma b,
    a1 =A[ sigma ]A> i1 ->
    a2 =A[ sigma ]A> i2 ->
    b = newComp "le" i1 i2 ->
    a1 <=' a2 =B[ sigma ]B> b
| e_greaterthan : forall a1 a2 i1 i2 sigma b,
    a1 =A[ sigma ]A> i1 ->
    a2 =A[ sigma ]A> i2 ->
    b = newComp "gt" i1 i2 ->
    a1 >' a2 =B[ sigma ]B> b
| e_greaterthan_eq : forall a1 a2 i1 i2 sigma b,
    a1 =A[ sigma ]A> i1 ->
    a2 =A[ sigma ]A> i2 ->
    b = newComp "ge" i1 i2 ->
    a1 >=' a2 =B[ sigma ]B> b
| e_nottrue : forall b sigma,
    b =B[ sigma ]B> boolType true ->
    (!' b) =B[ sigma ]B> boolType false
| e_notfalse : forall b sigma,
    b =B[ sigma ]B> boolType false ->
    (!' b) =B[ sigma ]B> boolType true
| e_andtrue : forall b1 b2 sigma t,
    b1 =B[ sigma ]B> boolType true ->
    b2 =B[ sigma ]B> t ->
    b1 &&' b2 =B[ sigma ]B> t
| e_andfalse : forall b1 b2 sigma,
    b1 =B[ sigma ]B>boolType false ->
    b1 &&' b2 =B[ sigma ]B> boolType false
| e_or : forall b1 b2 sigma t t1 t2,
    b1 =B[ sigma ]B> t1 ->
    b2 =B[ sigma ]B> t2 ->
    t = newOrB t1 t2 ->
    b1 ||' b2 =B[ sigma ]B> t
| e_equality : forall a1 a2 i1 i2 sigma b,
    a1 =A[ sigma ]A> i1 ->
    a2 =A[ sigma ]A> i2 ->
    b = newComp "eq" i1 i2 ->
    a1 ==' a2 =B[ sigma ]B> b
| e_inequality : forall a1 a2 i1 i2 sigma b,
    a1 =A[ sigma ]A> i1 ->
    a2 =A[ sigma ]A> i2 ->
    b = newComp "ineq" i1 i2 ->
    a1 !=' a2 =B[ sigma ]B> b
| e_xor : forall b1 b2 sigma t t1 t2,
    b1 =B[ sigma ]B> t1 ->
    b2 =B[ sigma ]B> t2 ->
    t = newXor t1 t2 ->
    b1 ||' b2 =B[ sigma ]B> t
| e_xand : forall b1 b2 sigma t t1 t2,
    b1 =B[ sigma ]B> t1 ->
    b2 =B[ sigma ]B> t2 ->
    t = newXand t1 t2 ->
    b1 ||' b2 =B[ sigma ]B> t
| e_tobool : forall a1 sigma i1 b,
    a1 =A[ sigma ]A> i1 ->
    b = newToBool i1 ->
    ToBool( a1 ) =B[ sigma ]B> b
where "B '=B[' S ']B>' B'" := (beval B S B').

Definition stack1 := update stack0 "x" (boolType true) (getMaxPos stack0).
Definition stack2 := update stack1 "y" (boolType false) (getMaxPos stack1).
Compute getAdress stack2 "x".
Compute getAdress stack2 "y".

Example ex_expr : ToNr("x") +' toNr(!' "y") =A[ stack2 ]A> nrType 2.
Proof. 
  eapply e_add.
  -eapply e_tonr. 
    +eapply e_bvar.
    +simpl. trivial.
  -eapply e_tonr. 
    +eapply e_notfalse. eapply e_bvar.
    +simpl. trivial.
  -simpl. trivial.
Qed.

Definition EqForTypes (a b : newType) : bool :=
match a, b with
| error, error => true
| nrType _, nrType _ => true
| boolType _, boolType _ => true
| strType _, strType _ => true
| code _, code _ => true
| _, _ => false
end.

Definition getStmt (cod : newType) : Stmt :=
match cod with
| code stmt => stmt
| _ => skip
end.

Reserved Notation "( L )-[ M1 ]=> M2" (at level 60).
Inductive stmt_eval : Stmt -> MemoryLayer -> MemoryLayer -> Prop :=
| st_skip : forall sigma,
   ( skip )-[ sigma ]=> sigma
| st_secv : forall s1 s2 sigma sigma1 sigma2,
   ( s1 )-[ sigma ]=> sigma1 ->
   ( s2 )-[ sigma1 ]=> sigma2 ->
   ( s1 ;; s2 )-[ sigma ]=> sigma2
| st_int : forall s a val sigma sigma1,
    val =A[ sigma ]A> a ->
    sigma1 = update sigma s a (getMaxPos sigma) ->
    ( int' s <-- val )-[ sigma ]=> sigma1
| st_bool : forall s b val sigma sigma1,
    val =B[ sigma ]B> b ->
    sigma1 = update sigma s b (getMaxPos sigma) ->
    ( bool' s <-- val)-[ sigma ]=> sigma1
| st_string : forall s val sigma sigma1 str,
    val =S[ sigma ]S> str ->
    sigma1 = update sigma s str (getMaxPos sigma) ->
    ( string' s <-- val )-[ sigma ]=> sigma1
| st_asigint : forall s a val sigma sigma1,
    EqForTypes (getVal sigma s) (nrType 0) = true ->
    val =A[ sigma ]A> a ->
    sigma1 = update sigma s a (getAdress sigma s) ->
    ( s :N= val )-[ sigma ]=> sigma1
| st_asigbool : forall s b val sigma sigma1,
    EqForTypes (getVal sigma s) (boolType false) = true ->
    val =B[ sigma ]B> b ->
    sigma1 = update sigma s b (getAdress sigma s) ->
    ( s :B= val )-[ sigma ]=> sigma1
| st_asigstring : forall s val sigma sigma1 str,
    EqForTypes (getVal sigma s) (strType str("") ) = true ->
    val =S[ sigma ]S> str ->
    sigma1 = update sigma s str (getAdress sigma s) ->
    ( s :S= val )-[ sigma ]=> sigma1
| st_iffalse : forall b s1 sigma,
    b =B[ sigma ]B> boolType false ->
    ( ifthen b s1 )-[ sigma ]=> sigma
| st_iftrue : forall b s1 sigma sigma1,
    b =B[ sigma ]B> boolType true ->
    ( s1 )-[ sigma ]=> sigma1 ->
    ( ifthen b s1 )-[ sigma ]=> sigma1
| st_ifelsefalse : forall b s1 s2 sigma sigma2,
    b =B[ sigma ]B> boolType false ->
    ( s2 )-[ sigma ]=> sigma2 ->
    ( ifthenelse b s1 s2 )-[ sigma ]=> sigma2
| st_ifelsetrue : forall b s1 s2 sigma sigma1,
    b =B[ sigma ]B> boolType true ->
    ( s1 )-[ sigma ]=> sigma1 ->
    ( ifthenelse b s1 s2 )-[ sigma ]=> sigma1
| st_whilefalse : forall b s sigma,
    b =B[ sigma ]B> boolType false ->
    ( whileloop b s )-[ sigma ]=> sigma
| st_whiletrue : forall b s sigma sigma1,
    b =B[ sigma ]B> boolType true ->
    ( s ;; whileloop b s )-[ sigma ]=> sigma1 ->
    ( whileloop b s )-[ sigma ]=> sigma1
| st_forloop_false : forall a b st s1 sigma sigma1,
    ( a )-[ sigma ]=> sigma1 ->
    b =B[ sigma1 ]B> boolType false ->
    ( forloop a b st s1 )-[ sigma ]=> sigma1
| st_forloop_true : forall a b st s1 sigma sigma1 sigma2,
    ( a )-[ sigma ]=> sigma1 ->
    (whileloop b (s1 ;; st) )-[ sigma1 ]=> sigma2 ->
    ( forloop a b st s1 )-[ sigma ]=> sigma2
| st_intpoint : forall V P sigma sigma1,
    EqForTypes (getVal sigma P) (nrType 0) = true ->
    sigma1 = update sigma V (getVal sigma P) (getAdress sigma P) ->
    ( int** V <-- P )-[ sigma ]=> sigma1
| st_boolpoint : forall V P sigma sigma1,
    EqForTypes (getVal sigma P) (boolType false) = true ->
    sigma1 = update sigma V (getVal sigma P) (getAdress sigma P) ->
    ( bool** V <-- P )-[ sigma ]=> sigma1
| st_strpoint : forall V P sigma sigma1,
    EqForTypes (getVal sigma P) (strType str("") ) = true ->
    sigma1 = update sigma V (getVal sigma P) (getAdress sigma P) ->
    ( string** V <-- P )-[ sigma ]=> sigma1
| st_intpoint_asig : forall V E i1 sigma sigma1,
    EqForTypes (getVal sigma V) (nrType 0) = true ->
    E =A[ sigma ]A> i1 ->
    sigma1 = update sigma V i1 (getAdress sigma V) ->
    ( n* V ::= E )-[ sigma ]=> sigma1 
| st_boolpoint_asig : forall V E i1 sigma sigma1,
    EqForTypes (getVal sigma V) (boolType false) = true ->
    E =B[ sigma ]B> i1 ->
    sigma1 = update sigma V i1 (getAdress sigma V) ->
   ( b* V ::= E )-[ sigma ]=> sigma1 
| st_strpoint_asig : forall V E i1 sigma sigma1,
    EqForTypes (getVal sigma V) (strType str("") ) = true ->
    E =S[ sigma ]S> i1 ->
    sigma1 = update sigma V i1 (getAdress sigma V) ->
   ( s* V ::= E )-[ sigma ]=> sigma1 
| st_callfun : forall s stmt sigma sigma1,
    stmt = getStmt (getVal sigma s ) ->
    ( stmt )-[ sigma ]=> sigma1 ->
    ( call s (( )) )-[ sigma ]=> sigma1
where "( L )-[ M1 ]=> M2" := (stmt_eval L M1 M2).

Example ex2 : exists stack', ( int' "x" <-- 10 ;;
                                int** "y" <-- "x" ;; 
                                n* "y" ::= 15 )-[ stack0 ]=> stack'
    /\ getVal stack' "x" = getVal stack' "y".
Proof.
  eexists.
  split.
  *eapply st_secv.
  -eapply st_int. eapply e_const. unfold update. simpl. trivial.
  -eapply st_secv.
    --eapply st_intpoint.
    +simpl. trivial.
    +unfold update. simpl. trivial.
    --eapply st_intpoint_asig.
    +simpl. trivial.
    +eapply e_const.
    +unfold update. simpl. trivial.
  *simpl. unfold updateMemory. simpl. trivial.
Qed.

Example ex3 : exists stack', ( bool' "x" <--false ;; "x" :B= true )-[ stack0 ]=> stack'
    /\ getVal stack' "x" = boolType true.
Proof.
  eexists. 
  split.
  *eapply st_secv.
  +eapply st_bool.
  -eapply e_false.
  -unfold update. simpl. trivial.
  +eapply st_asigbool.
  -simpl. trivial. 
  -eapply e_true.
  -unfold update. simpl. trivial.
  *simpl. unfold updateMemory. simpl. trivial.
Qed.

Reserved Notation "( L )-{ M1 }=> M2" (at level 60).
Inductive lang_eval : Lang -> MemoryLayer -> MemoryLayer -> Prop :=
| l_secv : forall s1 s2 sigma sigma1 sigma2,
   ( s1 )-{ sigma }=> sigma1 ->
   ( s2 )-{ sigma1 }=> sigma2 ->
   ( s1 ;' s2 )-{ sigma }=> sigma2
| l_int0 : forall s sigma sigma1,
  sigma1 = update sigma s (nrType 0) (getMaxPos sigma) ->
  ( int0' s )-{ sigma }=> sigma1
| l_bool0 : forall s sigma sigma1,
  sigma1 = update sigma s (boolType false) (getMaxPos sigma) ->
  ( bool0' s )-{ sigma }=> sigma1
| l_string0 : forall s sigma sigma1,
  sigma1 = update sigma s (strType str("") ) (getMaxPos sigma) ->
  ( string0' s )-{ sigma }=> sigma1
| l_funMain : forall stmt sigma sigma1,
  ( stmt )-[ sigma ]=> sigma1 ->
  ( void main() { stmt } )-{ sigma }=> sigma1
| l_function : forall s stmt sigma sigma1,
  sigma1 = update sigma s (code stmt) (getMaxPos sigma) ->
  ( void s (){ stmt } )-{ sigma }=> sigma1
where "( L )-{ M1 }=> M2" := (lang_eval L M1 M2).

Example ex4 : exists stack', 
  (int0' "x" ;' 
   bool0' "b" ;' 
   void main() {}
  )-{ stack0 }=> stack' 
        /\ getVal stack' "x" = nrType 0 /\ getVal stack' "b" = boolType false.
Proof.
  eexists.
  split.
  - eapply l_secv.
  + eapply l_int0. unfold update. simpl. trivial.
  + eapply l_secv. eapply l_bool0. unfold update. simpl. trivial.
  eapply l_funMain. eapply st_skip.
  -split ; unfold updateMemory ; simpl ; trivial.
Qed.

Definition sample1 := 
  int0' "x" ;' 
  void "fun" (){
    "x" :N= 100
  } ;'
  void main() {
     "x" :N= 654 ;;
     call "fun" (())
  }.
Example ex5 : exists stack', ( sample1 )-{ stack0 }=> stack' 
      /\ getVal stack' "x" = nrType 100.
Proof.
  eexists.  
  split.
  -unfold sample1. eapply l_secv.
    + eapply l_int0. unfold update. simpl. trivial.
    + eapply l_secv.
      ++ eapply l_function. unfold update. simpl. trivial.
      ++ eapply l_funMain.
        *eapply st_secv.
          **eapply st_asigint. simpl. trivial. 
            eapply e_const. unfold update. simpl. trivial.
          **eapply st_callfun. simpl. trivial. 
            eapply st_asigint. simpl. trivial.
            eapply e_const. unfold update. simpl. trivial.
   -simpl. unfold updateMemory. simpl. trivial.
Qed.
 
  


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

Inductive Pointer : Type :=
| NULL : Pointer
| pointtonr : nat -> Pointer
| pointtobool : nat -> Pointer
| pointtostring : nat -> Pointer.

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
| toNr : Var -> AExp (*transforma orice intr-un numar*)
| strLen : SExp -> AExp. (* returneaza lungimea unui string*)

Inductive BExp :=
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
| toBool : string -> BExp. (*transforma un numar in boolean*)

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
| point_nat : Var -> Var -> Stmt
| point_int : Var -> Var -> Stmt
| point_bool : Var -> Var -> Stmt
| point_str : Var -> Var -> Stmt
| refasig_nat : Var -> AExp -> Stmt
| refasig_int : Var -> AExp -> Stmt
| refasig_bool : Var -> BExp -> Stmt
| refasig_str : Var -> SExp -> Stmt
| decl_nat : Var -> AExp -> Stmt (*declarare nat cu o valoare specificata*)
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
| decl_nat0 : Var -> Lang (*declarare nat cu valoare default*)
| decl_int0 : Var -> Lang  (*declarare int cu valoare default*)
| decl_bool0 : Var -> Lang (*declarare bool cu valoare default*)
| decl_string0 : Var -> Lang(*declarare string cu valoare default*)
| functiaMain : Stmt -> Lang  (*functia principala main*)
| functie : Var -> list Var -> Stmt -> Lang. (*declarare de functii*)

Inductive newType : Type :=
| error : newType (*tip de eroare*)
| default : newType (*variabila contine valoarea default*)
| nrType : newNr -> newType (*variabila este de tip numar*)
| boolType : newBool -> newType (*variabila este de tip bool*)
| strType : newString -> newType (*variabila este de tip string*)
| pointerType : Pointer -> newType (*variabila este de tip pointer*)
| code : Stmt -> newType. (*codul unei funcii*)

Coercion code : Stmt >-> newType.

Notation "'uint**' V <-- P" := (point_nat V P) (at level 90).
Notation "'int**' V <-- P" := (point_int V P) (at level 90).
Notation "'bool**' V <-- P" := (point_bool V P) (at level 90).
Notation "'string**' V <-- P" := (point_str V P) (at level 90).

Notation "'u*' V ::= E" := (refasig_nat V E) (at level 90).
Notation "'i*' V ::= E" := (refasig_int V E) (at level 90).
Notation "'b*' V ::= E" := (refasig_bool V E) (at level 90).
Notation "'s*' V ::= E":= (refasig_str V E) (at level 90).

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
Notation "'void' N (( A1 , .. , An )){ }" := (functie N (cons (Id A1) .. (cons (Id An) nil) .. ) skip)(at level 95).
Notation "'void' N (( A1 , .. , An )){ S }" := (functie N (cons (Id A1) .. (cons (Id An) nil) .. ) S)(at level 95).

Notation "'call' N (( A1 , .. , An ))" := (apelfunc N (cons (Id A1) .. (cons (Id An) nil) .. ) ) (at level 89).
Notation "'call' N (( ))" := (apelfunc N nil) (at level 89).

Notation "'write(' S )" := (scrie S) (at level 92).
Notation "'read(' V )" := (citeste V) (at level 92).

(*secventa de cod cu pointeri*)
Check (uint** "to_nat" <-- "nr1" ;;
       int** "to_int" <-- "nr2" ;;
       bool** "to_bool" <-- "ok" ;;
       string** "to_str" <-- "msg" ;;
       u* "to_nat" ::= 10 ;;
       i* "to_int" ::= -5 ;;
       b* "to_bool" ::= true ;;
       s* "to_str" ::= str("mesaj !") ;;
       
       bool' "new" <-- false ;;
       "new" :B= true &&' b* "to_bool"
      ).

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

Definition updateState (st : State) (v : Var) (n : nat) : State:= 
fun x => if (Var_beq x v) then n else st x.

Definition updateMemory (mem : Memory) (n : nat) (val : newType) : Memory :=
fun n' => if (Nat.eqb n' n) then val else mem n'. 

Definition update (M : MemoryLayer) (V : Var) (T : newType) (pos : nat) : MemoryLayer :=
match M with
|<<st, mem, max>> => <<updateState st V pos, updateMemory mem pos T, (Nat.add max 1) >>
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
where "A '=A[' S ']A>' N" := (aeval A S N).

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

Reserved Notation "B '=B[' S ']B>' B'" (at level 70).
Inductive beval : BExp -> MemoryLayer -> newType -> Prop :=
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
where "B '=B[' S ']B>' B'" := (beval B S B').




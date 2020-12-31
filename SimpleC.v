Require Import Ascii String.
Require Import Coq.ZArith.BinInt.
Require Import Coq.Numbers.BinNums.
Require Import Coq.Lists.List.
Require Import Extraction.
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

Definition Z_of_bool (b : bool) := if b then 1 else 0.
Definition Z_of_ascii (a : ascii) : Z:=
  match a with
   Ascii b1 b2 b3 b4 b5 b6 b7 b8 =>
     Z_of_bool b1 + 2 * (Z_of_bool b2 + 2 * (Z_of_bool b3 + 2 * (Z_of_bool b4 + 2 *
      (Z_of_bool b5 + 2 * (Z_of_bool b6 + 2 * (Z_of_bool b7 + 2 * Z_of_bool b8))))))
  end.
Definition Z_of_0 := Eval compute in Z_of_ascii "0".
Definition Z_of_digit a := 
   let v := Z_of_ascii a - Z_of_0 in
   match v ?= 0 with
     Lt => None | Eq => Some v | 
     Gt => match v ?= 10 with Lt => Some v | _ => None end
   end.
Fixpoint str_to_num (s : string) : option (Z * Z) :=
  match s with
    EmptyString => None
  | String a s' => 
    match Z_of_digit a with
      None => None
    | Some va =>
      match str_to_num s' with
        None => Some (va, 1)
      | Some (vs, n) => Some (va * 10 ^ n + vs, n+1)
      end
    end
  end.
Definition num_to_newNr (n : option(Z*Z)) : newNr :=
match n with
| None => errNr
| Some (nr, _) => nrVal nr
end.
Definition str_toNewNr (s : string) : newNr :=
match s with
| EmptyString => errNr
| String a s' => if (ascii_dec a "-") 
        then (match (num_to_newNr (str_to_num s')) with
              | errNr => errNr
              | nrVal nr => nrVal (0 - nr) end
        ) 
        else (match (num_to_newNr (str_to_num s)) with
              | errNr => errNr
              | nrVal nr => nrVal nr end
        )
end.

Definition digit_to_ascii (n : Z) : ascii :=
match n with
|Z0 => "0"
|1 => "1"
|2 => "2"
|3 => "3"
|4 => "4"
|5 => "5"
|6 => "6"
|7 => "7"
|8 => "8"
|9 => "9"
|_ => ascii_of_nat 1
end.

Fixpoint nr_to_string_aux (time : nat) (n : Z) (acc : string) : string :=
  let acc' := String (digit_to_ascii (n mod 10)) acc in
  match time with
    | 0%nat => acc'
    | S time' =>
      match n / 10 with
        | 0 => acc'
        | n' => nr_to_string_aux time' n' acc'
      end
  end.

Definition nr_to_string (n : Z) : string :=
match n with
| Z0 => "0"
| Zpos _ => nr_to_string_aux 15 n ""
| Zneg l => String "-" (nr_to_string_aux 15 (Zpos l) "")
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
| boolToNr : BExp -> AExp (*transforma un bool intr-un numar*)
| strToNr : SExp -> AExp (*transforma un string intr-un numar*)
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
Notation "'BoolToNr(' B )" := (boolToNr B) (at level 0).
Notation "'StrToNr(' S )" := (strToNr S) (at level 0).
Notation "'ToBool(' S )" := (toBool S) (at level 0).
Notation "'ToStr(' S )" := (toString S) (at level 0).
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
Notation "A >=' B" := (mai_mareEq A B) (at level 52, left associativity).
Notation "A >' B" := (mai_mare A B) (at level 52, left associativity).
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
| caseOther : newNr -> Stmt -> Cases. (*alte cazuri*)

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

Coercion nrType : newNr >-> newType.
Coercion boolType : newBool >-> newType.
Coercion strType : newString >-> newType.
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

Definition EqForTypes (a b : newType) : bool :=
match a, b with
| error, error => true
| nrType _, nrType _ => true
| boolType _, boolType _ => true
| strType _, strType _ => true
| code _, code _ => true
| _, _ => false
end.

Definition Memory := nat -> newType.
Definition State := Var -> nat.
Inductive MemoryLayer := 
| pair : State -> Memory -> nat -> State -> Memory -> nat -> MemoryLayer.
Notation "<< S , M , N >>-<< GS , GM , GN >>" := (pair S M N GS GM GN) (at level 0).

Definition getVal (m : MemoryLayer) (v : Var) : newType :=
match m with
| pair st mem _ gst gmem _ => if (EqForTypes ( mem (st v) ) error) 
                              then gmem(gst v) else mem(st v)
end.

Definition getLocalMaxPos (m : MemoryLayer) : nat :=
match m with
| pair _ _ max _ _ _  => max
end.

Definition getGlobalMaxPos (m : MemoryLayer) : nat :=
match m with
| pair _ _ _ _ _ max  => max
end.

Definition getLocalAdress (m:MemoryLayer) (v : Var) : nat :=
match m with
| pair state _ _ _ _ _ => state v
end.

Definition getGlobalAdress (m:MemoryLayer) (v:Var) : nat :=
match m with
| pair _ _ _ state _ _ => state v
end.

Definition getAdress (m:MemoryLayer) (v:Var) : nat :=
match m with
| pair st _ _ gst _ _ => if (Nat.eqb (st v) 0%nat) then gst v else st v
end.

Definition updateState (st : State) (v : Var) (n : nat) : State:= 
fun x => if (Var_beq x v) then n else st x.

Definition updateMemory (mem : Memory) (n : nat) (val : newType) : Memory :=
fun n' => if (Nat.eqb n' n) then val else mem n'. 

Definition updateLocal (M : MemoryLayer) (V : Var) (T : newType) (pos : nat) : MemoryLayer :=
match M with
|<<st, mem, max>>-<<gst, gmem, gmax>> => if (andb (Nat.eqb pos (getLocalAdress M V) ) (Nat.eqb pos 0) ) then
       <<st, mem, max>>-<<gst, gmem, gmax>> else
       <<updateState st V pos, updateMemory mem pos T, 
      (if (Nat.ltb pos max) then max else Nat.add max 1) >>-<<gst, gmem, gmax>>
end.

Definition updateGlobal (M : MemoryLayer) (V : Var) (T : newType) (pos : nat) : MemoryLayer :=
match M with
|<<st, mem, max>>-<<gst, gmem, gmax>> => if (andb (Nat.eqb pos (getGlobalAdress M V) ) (Nat.eqb pos 0) ) then
       <<st, mem, max>>-<<gst, gmem, gmax>> else
       <<st, mem, max>>-<<updateState gst V pos, updateMemory gmem pos T, 
      (if (Nat.ltb pos gmax) then gmax else Nat.add gmax 1) >>
end.

Definition updateLocalAtAdress (M : MemoryLayer) (addr : nat) (T : newType): MemoryLayer :=
match M with
|<<st, mem, max>>-<<gst, gmem, gmax>> => if (Nat.eqb addr 0) then
       <<st, mem, max>>-<<gst, gmem, gmax>> else
       <<st, updateMemory mem addr T, max >>-<<gst, gmem, gmax>>
end.

Definition updateGlobalAtAdress (M : MemoryLayer) (addr : nat) (T : newType): MemoryLayer :=
match M with
|<<st, mem, max>>-<<gst, gmem, gmax>> => if (Nat.eqb addr 0) then
       <<st, mem, max>>-<<gst, gmem, gmax>> else
       <<st, mem, max>>-<<gst, updateMemory gmem addr T, gmax >>
end.

Definition updateAtAdress (M : MemoryLayer) (addr : nat) (T : newType) : MemoryLayer :=
match M with
|<<st, mem, max>>-<<gst, gmem, gmax>> => if (EqForTypes (mem addr) error)
                                         then updateGlobalAtAdress M addr T
                                         else updateLocalAtAdress M addr T
end.

 
Definition mem0 : Memory := fun n => error.
Definition state0 : State := fun x => 0%nat.
Definition stack0 := <<state0, mem0, 1>>-<<state0, mem0, 1>>.

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
|nrType n => nrType n
|boolType a' => match a' with
                | errBool => nrType errNr
                | boolVal b => if (b) then (nrType 1) else (nrType 0)
                end
|strType s' => match s' with 
               | strVal s => str_toNewNr s
               | errStr => nrType errNr
               end
|_ => nrType errNr
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
| boolType b => boolType b
| nrType a' => match a' with
                | errNr => boolType errBool
                | nrVal n => if (Z.eqb n 0) then (boolType false) else (boolType true)
                end
| strType s => match s with
               | strVal s'=> if (string_dec s' "true") then (boolType true) 
                              else (boolType false)
               | errStr => boolType errBool
               end
|_ => boolType errBool
end.

Definition newToStr (a : newType) :=
match a with 
| boolType b => match b with 
                | errBool => errString
                | boolVal b' => if (b') then str("true") else str("false")
                end
| strType s => strType s
| nrType n => match n with
              | errNr => errString
              | nrVal n' => str(nr_to_string n')
              end
| _ => strType errString
end.

Compute newToStr (nrType 10).


Reserved Notation "STR '=S[' St ']S>' N" (at level 60).
Inductive seval : SExp -> MemoryLayer -> newType -> Prop :=
| s_const : forall s sigma, sconst s =S[ sigma ]S> strType s
| s_var : forall s sigma, svar s =S[ sigma ]S> getVal sigma s
| s_concat : forall s1 s2 sigma s st1 st2,
    s1 =S[ sigma ]S> st1 ->
    s2 =S[ sigma ]S> st2 ->
    s = newStrcat st1 st2 ->
    Concat( s1 , s2 ) =S[ sigma ]S> s
| s_tostr : forall s1 sigma t1 a,
    t1 = getVal sigma s1 ->
    a = newToStr t1 ->
    ToStr( s1 ) =S[ sigma ]S> a
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
| e_booltonr : forall b1 sigma t1 a,
    b1 =B[ sigma ]B> t1 ->
    a = newToNr t1 ->
    BoolToNr( b1 ) =A[ sigma ]A> a
| e_strtonr : forall s1 sigma t1 a,
    s1 =S[ sigma ]S> t1 ->
    a = newToNr t1 ->
    StrToNr( s1 ) =A[ sigma ]A> a
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

Definition stack1 := updateLocal stack0 "x" (boolType true) (getLocalMaxPos stack0).
Definition stack2 := updateLocal stack1 "y" (boolType false) (getLocalMaxPos stack1).
Compute getLocalAdress stack2 "x".
Compute getLocalAdress stack2 "y".

Example ex_expr : BoolToNr("x") +' BoolToNr(!' "y") =A[ stack2 ]A> nrType 2.
Proof. 
  eapply e_add.
  -eapply e_booltonr.
    + eapply e_bvar.
    +simpl. trivial.
  -eapply e_booltonr. 
    +eapply e_notfalse. eapply e_bvar.
    +simpl. trivial.
  -simpl. trivial.
Qed.

Definition getStmt (cod : newType) : Stmt :=
match cod with
| code stmt => stmt
| _ => skip
end.

Definition TypeToBool (b : newType) : bool :=
match b with
| boolType b' => match b' with
                 |boolVal bo => bo
                 |errBool => false
                 end
| _ => false
end.

Definition get_caseStmt (C : Cases) : Stmt :=
match C with
| default:{ s }; => s
| case( _ ):{ s }; => s
end.

Definition checkCase (C : Cases ) (n : newType) : bool :=
match C with
| default:{ _ }; => true
| case( a ):{ _ }; => TypeToBool (newComp "eq" a n)
end.

Fixpoint get_switch_case (n : newType) (cl : list Cases) : Stmt :=
match n with
| nrVal n' => match cl with 
              | nil => skip
              | x :: next => if (checkCase x n) then (get_caseStmt x) else (get_switch_case n next)
              end
| _ => skip
end.
 
Reserved Notation " L -[ M1 ]=> M2" (at level 60).
Inductive stmt_eval : Stmt -> MemoryLayer -> MemoryLayer -> Prop :=
| st_skip : forall sigma,
   ( skip )-[ sigma ]=> sigma
| st_secv : forall s1 s2 sigma sigma1 sigma2,
   ( s1 )-[ sigma ]=> sigma1 ->
   ( s2 )-[ sigma1 ]=> sigma2 ->
   ( s1 ;; s2 )-[ sigma ]=> sigma2
| st_int : forall s a val sigma sigma1,
    val =A[ sigma ]A> a ->
    sigma1 = updateLocal sigma s a (getLocalMaxPos sigma) ->
    ( int' s <-- val )-[ sigma ]=> sigma1
| st_bool : forall s b val sigma sigma1,
    val =B[ sigma ]B> b ->
    sigma1 = updateLocal sigma s b (getLocalMaxPos sigma) ->
    ( bool' s <-- val)-[ sigma ]=> sigma1
| st_string : forall s val sigma sigma1 str,
    val =S[ sigma ]S> str ->
    sigma1 = updateLocal sigma s str (getLocalMaxPos sigma) ->
    ( string' s <-- val )-[ sigma ]=> sigma1
| st_asigint : forall s a val sigma sigma1,
    EqForTypes (getVal sigma s) (nrType 0) = true ->
    val =A[ sigma ]A> a ->
    sigma1 = updateAtAdress sigma (getAdress sigma s) a ->
    ( s :N= val )-[ sigma ]=> sigma1
| st_asigbool : forall s b val sigma sigma1,
    EqForTypes (getVal sigma s) (boolType false) = true ->
    val =B[ sigma ]B> b ->
    sigma1 = updateAtAdress sigma (getAdress sigma s) b ->
    ( s :B= val )-[ sigma ]=> sigma1
| st_asigstring : forall s val sigma sigma1 str,
    EqForTypes (getVal sigma s) (strType str("") ) = true ->
    val =S[ sigma ]S> str ->
    sigma1 = updateAtAdress sigma (getAdress sigma s) str  ->
    ( s :S= val )-[ sigma ]=> sigma1
| st_iffalse : forall b s1 sigma,
    b =B[ sigma ]B> false ->
    ( ifthen b s1 )-[ sigma ]=> sigma
| st_iftrue : forall b s1 sigma sigma1,
    b =B[ sigma ]B> true ->
    ( s1 )-[ sigma ]=> sigma1 ->
    ( ifthen b s1 )-[ sigma ]=> sigma1
| st_ifelsefalse : forall b s1 s2 sigma sigma2,
    b =B[ sigma ]B> false ->
    ( s2 )-[ sigma ]=> sigma2 ->
    ( ifthenelse b s1 s2 )-[ sigma ]=> sigma2
| st_ifelsetrue : forall b s1 s2 sigma sigma1,
    b =B[ sigma ]B> true ->
    ( s1 )-[ sigma ]=> sigma1 ->
    ( ifthenelse b s1 s2 )-[ sigma ]=> sigma1
| st_whilefalse : forall b s sigma,
    b =B[ sigma ]B> false ->
    ( whileloop b s )-[ sigma ]=> sigma
| st_whiletrue : forall b s sigma sigma1,
    b =B[ sigma ]B> true ->
    ( s ;; whileloop b s )-[ sigma ]=> sigma1 ->
    ( whileloop b s )-[ sigma ]=> sigma1
| st_forloop_false : forall a b st s1 sigma sigma1,
    ( a )-[ sigma ]=> sigma1 ->
    b =B[ sigma1 ]B> false ->
    ( forloop a b st s1 )-[ sigma ]=> sigma1
| st_forloop_true : forall a b st s1 sigma sigma1 sigma2,
    ( a )-[ sigma ]=> sigma1 ->
    (whileloop b (s1 ;; st) )-[ sigma1 ]=> sigma2 ->
    ( forloop a b st s1 )-[ sigma ]=> sigma2
| st_intpoint : forall V P sigma sigma1,
    EqForTypes (getVal sigma P) (nrType 0) = true ->
    sigma1 = updateLocal sigma V (getVal sigma P) (getAdress sigma P) ->
    ( int** V <-- P )-[ sigma ]=> sigma1
| st_boolpoint : forall V P sigma sigma1,
    EqForTypes (getVal sigma P) (boolType false) = true ->
    sigma1 = updateLocal sigma V (getVal sigma P) (getAdress sigma P) ->
    ( bool** V <-- P )-[ sigma ]=> sigma1
| st_strpoint : forall V P sigma sigma1,
    EqForTypes (getVal sigma P) (strType str("") ) = true ->
    sigma1 = updateLocal sigma V (getVal sigma P) (getAdress sigma P) ->
    ( string** V <-- P )-[ sigma ]=> sigma1
| st_intpoint_asig : forall V E i1 sigma sigma1,
    EqForTypes (getVal sigma V) (nrType 0) = true ->
    E =A[ sigma ]A> i1 ->
    sigma1 = updateAtAdress sigma (getLocalAdress sigma V) i1  ->
    ( n* V ::= E )-[ sigma ]=> sigma1 
| st_boolpoint_asig : forall V E i1 sigma sigma1,
    EqForTypes (getVal sigma V) (boolType false) = true ->
    E =B[ sigma ]B> i1 ->
    sigma1 = updateAtAdress sigma (getAdress sigma V) i1 ->
   ( b* V ::= E )-[ sigma ]=> sigma1 
| st_strpoint_asig : forall V E i1 sigma sigma1,
    EqForTypes (getVal sigma V) (strType str("") ) = true ->
    E =S[ sigma ]S> i1 ->
    sigma1 = updateAtAdress sigma (getAdress sigma V) i1  ->
   ( s* V ::= E )-[ sigma ]=> sigma1 
| st_callfun : forall s l stmt sigma sigma1,
    stmt = getStmt (getVal sigma s ) ->
    ( stmt )-[ sigma ]=> sigma1 ->
    ( apelfunc s l )-[ sigma ]=> sigma1
| st_switch : forall a cl sigma n v sigma',
    a =A[ sigma ]A> n ->
    v = (get_switch_case n cl) ->
    v -[ sigma ]=> sigma' ->
    switch a cl -[ sigma ]=> sigma'
| st_dowhile_true : forall st b sigma sigma' sigma'',
    st -[ sigma ]=> sigma' ->
    b =B[ sigma' ]B> true ->
    ( whileloop b st ) -[ sigma' ]=> sigma'' ->
    do'{ st }while( b ) -[ sigma ]=> sigma'
| st_dowhile_false : forall st b sigma sigma',
    st -[ sigma ]=> sigma' ->
    b =B[ sigma' ]B> false ->
    do'{ st }while( b ) -[ sigma ]=> sigma'
where "L -[ M1 ]=> M2" := (stmt_eval L M1 M2).

Example ex2 : exists stack', ( int' "x" <-- 10 ;;
                                int** "y" <-- "x" ;; 
                                n* "y" ::= 15 ) -[ stack0 ]=> stack'
    /\ getVal stack' "x" = getVal stack' "y".
Proof.
  eexists.
  split.
  *eapply st_secv.
  -eapply st_int. eapply e_const. unfold updateLocal. simpl. trivial.
  -eapply st_secv.
    --eapply st_intpoint.
    +simpl. trivial.
    +unfold updateLocal. simpl. trivial.
    --eapply st_intpoint_asig.
    +simpl. trivial.
    +eapply e_const.
    +unfold updateLocal. simpl. trivial.
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
  -unfold updateLocal. simpl. trivial.
  +eapply st_asigbool.
  -simpl. trivial. 
  -eapply e_true.
  -unfold updateAtAdress. simpl. trivial.
  *simpl. unfold updateMemory. simpl. trivial.
Qed.

Reserved Notation "L -{ M1 }=> M2" (at level 60).
Inductive lang_eval : Lang -> MemoryLayer -> MemoryLayer -> Prop :=
| l_secv : forall s1 s2 sigma sigma1 sigma2,
   ( s1 )-{ sigma }=> sigma1 ->
   ( s2 )-{ sigma1 }=> sigma2 ->
   ( s1 ;' s2 )-{ sigma }=> sigma2
| l_int0 : forall s sigma sigma1,
  sigma1 = updateGlobal sigma s (nrType 0) (getGlobalMaxPos sigma) ->
  ( int0' s )-{ sigma }=> sigma1
| l_bool0 : forall s sigma sigma1,
  sigma1 = updateGlobal sigma s (boolType false) (getGlobalMaxPos sigma) ->
  ( bool0' s )-{ sigma }=> sigma1
| l_string0 : forall s sigma sigma1,
  sigma1 = updateGlobal sigma s (strType str("") ) (getGlobalMaxPos sigma) ->
  ( string0' s )-{ sigma }=> sigma1
| l_funMain : forall stmt sigma sigma1,
  ( stmt )-[ sigma ]=> sigma1 ->
  ( void main() { stmt } )-{ sigma }=> sigma1
| l_function : forall s stmt sigma sigma1,
  sigma1 = updateGlobal sigma s (code stmt) (getGlobalMaxPos sigma) ->
  ( void s (){ stmt } )-{ sigma }=> sigma1
where "L -{ M1 }=> M2" := (lang_eval L M1 M2).

Example ex4 : exists stack', 
  (int0' "x" ;' 
   bool0' "b" ;' 
   void main() {}
  )-{ stack0 }=> stack' 
        /\ getVal stack' "x" = 0 /\ getVal stack' "b" = false.
Proof.
  eexists.
  split.
  - eapply l_secv.
  + eapply l_int0. unfold updateGlobal. simpl. trivial.
  + eapply l_secv. eapply l_bool0. unfold updateGlobal. simpl. trivial.
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
      /\ getVal stack' "x" = 100.
Proof.
  eexists.  
  split.
  -unfold sample1. eapply l_secv.
    + eapply l_int0. unfold updateGlobal. simpl. trivial.
    + eapply l_secv.
      ++ eapply l_function. unfold updateGlobal. simpl. trivial.
      ++ eapply l_funMain.
        *eapply st_secv.
          **eapply st_asigint. simpl. trivial. 
            eapply e_const. unfold updateAtAdress. simpl. trivial.
          **eapply st_callfun. simpl. trivial. 
            eapply st_asigint. simpl. trivial.
            eapply e_const. unfold updateAtAdress. simpl. trivial.
   -simpl. unfold updateMemory. simpl. trivial.
Qed.

Example ex6 : exists stack', 
              (
                int' "x" <-- 0 ;;
                do'{
                   "x" :N= "x" +' 2
                }while("x" <' 0)
              )-[ stack0 ]=> stack'
    /\ getVal stack' "x" = 2.
Proof.
  eexists.
  split.
  -eapply st_secv.
    +eapply st_int. eapply e_const. unfold updateLocal. simpl. trivial.
    +eapply st_dowhile_false. 
      *eapply st_asigint. simpl. trivial.
       eapply e_add. eapply e_var. eapply e_const. simpl. trivial.
       unfold updateLocal. simpl. trivial.
      *eapply e_lessthan. eapply e_var. eapply e_const.
       simpl. unfold Z.ltb. simpl. trivial.
  -unfold updateMemory. simpl. trivial.
Qed.

Definition switch1 := (
  int0' "x" ;'
  void main() {
     "x" :N= 5 ;;
     switch'( "x" ){ 
        case( 1 ):{ skip };
        case( 3 ):{ "x" :N= 100 };
        case( 5 ):{ "x" :N= 50 };
        case( 7 ):{ bool' "y" <-- true};
        default:{ "x" :N= 0 };
     }end
  }
).

Check switch1.

Example ex_switch : exists stack', switch1 -{ stack0 }=> stack'
        /\ getVal stack' "x" = 50.
Proof.
  eexists.
  unfold switch1.
  split.
  -eapply l_secv.
    +eapply l_int0. unfold updateGlobal. simpl. trivial.
    +eapply l_funMain. eapply st_secv.
      *eapply st_asigint. simpl. trivial. eapply e_const. unfold updateAtAdress. simpl. trivial.
      *eapply st_switch. eapply e_var. simpl. trivial.
      eapply st_asigint. trivial. eapply e_const. trivial.
  -simpl. unfold updateMemory. simpl. reflexivity.
Qed.
  


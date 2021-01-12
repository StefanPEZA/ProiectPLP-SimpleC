Require Import Ascii String.
Require Import Coq.ZArith.BinInt.
Require Import Coq.Numbers.BinNums.
Require Import Coq.Lists.List.
Require Import Extraction.
Import ListNotations.
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
|Z0 => "0" |1 => "1" |2 => "2" |3 => "3"
|4 => "4" |5 => "5" |6 => "6"
|7 => "7" |8 => "8" |9 => "9"
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

Definition notZ (a : Z) : Z := if (Z.eqb a 0) then 1 else 0.

Definition toZ (b : bool) : Z :=
match b with
| true => 1
| false => 0
end.

Definition toB (a : Z) : bool := if (Z.eqb a 0) then false else true.


Definition aenv0 : Var -> Z := 
  fun x => 0.

Definition update (env : Var -> Z) (v : Var) (n : Z) : Var -> Z :=
  fun var : Var => 
      if (Var_beq var v) 
      then n
      else (env var).

Definition aenv1 := update aenv0 "x" 10.

Definition aexpZ (a : newNr) : Z :=
match a with 
|nrVal n => n
| _ => 0
end.

Definition bexpZ (b : newBool) : Z :=
match b with 
|boolVal b => (toZ b)
| _ => 0
end.

Fixpoint interpretA (a : AExp) (env : Var -> Z) : Z :=
  match a with
  | avar k => env k
  | aconst c => aexpZ c
  | adunare a1 a2 => (interpretA a1 env) + (interpretA a2 env)
  | scadere a1 a2 => (interpretA a1 env) - (interpretA a2 env)
  | inmultire a1 a2 => (interpretA a1 env) * (interpretA a2 env)
  | impartire a1 a2 => (interpretA a1 env) / (interpretA a2 env)
  | modulo a1 a2 => Z.modulo (interpretA a1 env) (interpretA a2 env)
  | _ => 0
  end.

Fixpoint interpretB (b : BExp) (env : Var -> Z) : Z :=
  match b with
  | bvar k => env k
  | bconst c => bexpZ c
  | mai_micEq a1 a2 => toZ(Z.leb (interpretA a1 env) (interpretA a2 env))
  | mai_mic a1 a2 => toZ(Z.ltb (interpretA a1 env) (interpretA a2 env))
  | mai_mareEq a1 a2 => toZ(Z.leb (interpretA a2 env) (interpretA a1 env))
  | mai_mare a1 a2 => toZ(Z.ltb (interpretA a2 env) (interpretA a1 env))
  | si_logic a1 a2 => toZ(andb (toB(interpretB a1 env)) (toB(interpretB a2 env)))
  | sau_logic a1 a2 => toZ(orb (toB(interpretB a1 env)) (toB(interpretB a2 env)))
  | negatie b' => notZ (interpretB b' env)
  | egalitate a1 a2 => toZ( Z.eqb (interpretA a1 env) (interpretA a2 env) )
  | inegalitate a1 a2 => notZ (toZ( Z.eqb (interpretA a1 env) (interpretA a2 env) ))
  | _ => 0
  end.

(*limbaj de asamblare*)
Inductive Instruction :=
| push_const : Z -> Instruction
| push_var : Var -> Instruction
| pop : Var -> Instruction
| add : Instruction
| mul : Instruction
| sub : Instruction
| div : Instruction
| modu : Instruction
| lt : Instruction
| lte : Instruction
| gt : Instruction
| gte : Instruction
| eq : Instruction
| neq : Instruction
| or : Instruction
| and : Instruction
| not : Instruction.

Definition Stack := list Z.
Definition run_instruction (i : Instruction) 
          (env : Var -> Z) (stack : Stack) : Stack :=
  match i with
  | push_const c => (c :: stack)
  | push_var x => ((env x) :: stack)
  | pop x => match stack with
             | l :: stack' => stack'
             | _ => stack
             end
  | add => match stack with 
           | n1 :: n2 :: stack' => (n2 + n1) :: stack'
           | _ => stack
           end
  | mul => match stack with 
           | n1 :: n2 :: stack' => (n2 * n1) :: stack'
           | _ => stack
           end
  | sub => match stack with 
           | n1 :: n2 :: stack' => (n2 - n1) :: stack'
           | _ => stack
           end
  | div => match stack with 
           | n1 :: n2 :: stack' => (n2 / n1) :: stack'
           | _ => stack
           end
  | modu => match stack with 
           | n1 :: n2 :: stack' => (Z.modulo n2 n1) :: stack'
           | _ => stack
           end
  | lt => match stack with 
          | n1 :: n2 :: stack' => toZ(Z.ltb n2 n1) :: stack'
          | _ => stack
          end
  | lte => match stack with 
          | n1 :: n2 :: stack' => toZ(Z.leb n2 n1) :: stack'
          | _ => stack
          end
  | gt => match stack with 
          | n1 :: n2 :: stack' => toZ(Z.ltb n1 n2) :: stack'
          | _ => stack
          end
  | gte => match stack with 
          | n1 :: n2 :: stack' => toZ(Z.leb n1 n2) :: stack'
          | _ => stack
          end
  | eq => match stack with 
          | n1 :: n2 :: stack' => toZ(Z.eqb n2 n1) :: stack'
          | _ => stack
          end
  | neq => match stack with 
          | n1 :: n2 :: stack' => notZ(toZ(Z.eqb n2 n1)) :: stack'
          | _ => stack
          end
  | or => match stack with 
          | b1 :: b2 :: stack' => toZ(orb (toB b1) (toB b2) ) :: stack'
          | _ => stack
          end
  | and => match stack with 
          | b1 :: b2 :: stack' => toZ(andb (toB b1) (toB b2) ) :: stack'
          | _ => stack
          end
  | not => match stack with 
          | b :: stack' => notZ b :: stack'
          | _ => stack
          end
  end.


Fixpoint run_instructions (is' : list Instruction) 
          (env : Var -> Z) (stack : Stack) : Stack :=
  match is' with
  | [] => stack
  | pop x :: is'' => match stack with
                    | n :: stack' => 
                run_instructions is'' (update env x n) (run_instruction (pop x) env stack)
                    | _ => run_instructions is'' env (run_instruction (pop x) env stack)
                    end
  | i :: is'' => run_instructions is'' env (run_instruction i env stack)
  end.

Definition pgm1 := [
    push_const 10;
    push_const 60;
    pop "a" ;       (*a = 60*)
    pop "b" ;       (*b = 10*)
    push_var "b" ;  (*10*)
    push_var "a" ;  (*60*)
    sub ;           (*10 - 60 = -50*)
    pop "x" ;       (*x = -50*)
    push_var "a" ;  (*10*)
    push_var "b" ;  (*60*)
    add ;           (*10 + 60 = 70*)
    push_var "x"    (*-50*) ;
    gt
].
Compute run_instructions pgm1 aenv0 [].

(*compilator*)
Fixpoint compileA (ae : AExp) : list Instruction :=
match ae with
  | aconst c => [push_const (aexpZ c)]
  | avar v => [push_var v]
  | adunare e1 e2 => (compileA e1) ++ (compileA e2) ++ [add]
  | inmultire e1 e2 => (compileA e1) ++ (compileA e2) ++ [mul]
  | scadere e1 e2 => (compileA e1) ++ (compileA e2) ++ [sub]
  | impartire e1 e2 => (compileA e1) ++ (compileA e2) ++ [div]
  | modulo e1 e2 => (compileA e1) ++ (compileA e2) ++ [modu]
  | _ => [push_const 0]
end.

Fixpoint compileB (be : BExp) : list Instruction :=
match be with
  | bconst c => [push_const (bexpZ c)]
  | bvar v => [push_var v]
  | negatie B => (compileB B ) ++ [not]
  | si_logic B1 B2 => (compileB B1) ++ (compileB B2) ++ [and]
  | sau_logic B1 B2 => (compileB B1) ++ (compileB B2) ++ [or]
  | mai_mic A1 A2 => (compileA A1) ++ (compileA A2) ++ [lt]
  | mai_micEq A1 A2 => (compileA A1) ++ (compileA A2) ++ [lte]
  | mai_mare A1 A2 => (compileA A1) ++ (compileA A2) ++ [gt]
  | mai_mareEq A1 A2 => (compileA A1) ++ (compileA A2) ++ [gte]
  | egalitate A1 A2 => (compileA A1) ++ (compileA A2) ++ [eq]
  | inegalitate A1 A2 => (compileA A1) ++ (compileA A2) ++ [neq]
  | _ => [push_const 0]
end.

Compute compileA (10 -' 2 *' 2 *' 2).
Compute run_instructions (compileA (10 -' 2 *' 2 *' 2)) aenv1 [].

Compute compileB ((10 -' 2 *' 2 *' 2) <' 130 %' 7).
Compute (compileA (130 %' 7)).
Compute run_instructions (compileA (130 %' 7)) aenv1 [].
Compute run_instructions (compileB ((10 -' 2 *' 2 *' 2) <' 130 %' 7)) aenv1 [].

Require Import Bool.
(*certificare*)
Lemma soundness_helper_A : 
    forall e env stack is',
      run_instructions (compileA e ++ is') env stack =
      run_instructions is' env ((interpretA e env) :: stack).
Proof.
    induction e; intros; simpl; trivial; rewrite <- app_assoc; rewrite <- app_assoc;
    rewrite IHe1; rewrite IHe2; simpl; trivial.
Qed.

Theorem soundness_A :
    forall e env,
      run_instructions (compileA e) env [] = 
        [interpretA e env].
Proof. 
    intros.
    rewrite <- app_nil_r with (l := (compileA e)).
    rewrite soundness_helper_A.
    simpl. trivial.
Qed.

Lemma soundness_helper_B : 
    forall e env stack is',
      run_instructions (compileB e ++ is') env stack =
      run_instructions is' env ((interpretB e env) :: stack).
Proof.
    induction e; intros; trivial; 
    simpl; rewrite <- app_assoc.
    -rewrite IHe. simpl. trivial.
    -rewrite <- app_assoc. rewrite IHe1. rewrite IHe2. simpl.
    rewrite andb_comm. trivial.
    -rewrite <- app_assoc. rewrite IHe1. rewrite IHe2. simpl.
    rewrite orb_comm. trivial.
    -rewrite <- app_assoc. simpl. rewrite soundness_helper_A.
    rewrite soundness_helper_A. simpl. trivial.
    -rewrite <- app_assoc. simpl. rewrite soundness_helper_A.
    rewrite soundness_helper_A. simpl. trivial.
    -rewrite <- app_assoc. simpl. rewrite soundness_helper_A.
    rewrite soundness_helper_A. simpl. trivial.
    -rewrite <- app_assoc. simpl. rewrite soundness_helper_A.
    rewrite soundness_helper_A. simpl. trivial.
    -rewrite <- app_assoc. simpl. rewrite soundness_helper_A.
    rewrite soundness_helper_A. simpl. trivial.
    -rewrite <- app_assoc. simpl. rewrite soundness_helper_A.
    rewrite soundness_helper_A. simpl. trivial.
Qed.

Theorem soundness_B :
    forall e env,
      run_instructions (compileB e) env [] = 
        [interpretB e env].
Proof.
  intros.
   rewrite <- app_nil_r with (l := (compileB e)).
    rewrite soundness_helper_B.
    simpl. trivial.
Qed.
  
--stop--
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
| Return : Stmt (*instructune obligatorie la finalul unei functii*)
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
| pointer : nat -> bool -> newType (*pointer*)
| code : list Var -> Stmt -> newType. (*codul unei funcii*)

Coercion nrType : newNr >-> newType.
Coercion boolType : newBool >-> newType.
Coercion strType : newString >-> newType.

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

Notation "'void' N (){ }" := (functie N nil Return)(at level 95).
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
| pointer _ _, pointer _ _ => true
| code _ _, code _ _ => true
| _, _ => false
end.

Definition Memory := nat -> newType.
Definition State := Var -> nat.
Inductive MemoryLayer := 
| pair : State -> Memory -> nat -> State -> Memory -> nat -> MemoryLayer.
Notation "<< S , M , N >>-<< GS , GM , GN >>" := (pair S M N GS GM GN) (at level 0).

Definition isLocal (m : MemoryLayer) (v : Var) : bool :=
match m with
| pair st mem _ gst gmem _ => if andb (Nat.eqb (st v) 0%nat) (EqForTypes ( mem (st v) ) error) 
                              then false else true
end.

Definition getVal (m : MemoryLayer) (v : Var) : newType :=
match m with
| pair st mem _ gst gmem _ => if (isLocal m v) 
                              then mem(st v) else gmem(gst v)
end.

Definition getPointerAdress (a : newType) : nat :=
match a with
| pointer nr _ => nr
| _ => 0
end.

Definition isPointerLocal (a : newType) : bool :=
match a with
| pointer _ isl => isl
| _ => false
end.

Definition getPointerVal (m : MemoryLayer) (p : Var) : newType :=
let point := getVal m p in
match point with
| pointer nr isl => match m with
                    | pair _ mem _ _ gmem _ => if (isl) then
                                              (mem nr ) else (gmem nr)
                    end 
| _ => error
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

Definition updateAtAdress (M : MemoryLayer) (isL : bool) (addr : nat) (T : newType) : MemoryLayer :=
match M with
|<<st, mem, max>>-<<gst, gmem, gmax>> => if isL
                                         then updateLocalAtAdress M addr T
                                         else updateGlobalAtAdress M addr T
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
| code _ stmt => stmt
| _ => skip
end.

Definition getArgs (cod : newType) : list Var :=
match cod with
| code args _ => args
| _ => nil
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

Definition MergeMemory (l g: MemoryLayer) : MemoryLayer :=
match l, g with
|<<st1, mem1, max1>>-<<gst1, gmem1, gmax1>>, 
    <<st2, mem2, max2>>-<<gst2, gmem2, gmax2>> => <<st1, mem1, max1>>-<<gst2, gmem2, gmax2>>
end.

Definition DeleteLocal (m:MemoryLayer ) : MemoryLayer :=
match m with 
| <<st, mem, max>>-<<gst, gmem, gmax>> => <<state0, mem0, 1>>-<<gst, gmem, gmax>>
end.

Fixpoint NewLocalStack (l1 l2 : list Var) (m save:MemoryLayer): MemoryLayer :=
match l1, l2 with
| nil , nil => save
| x :: nil, y :: nil => updateLocal save y (getVal m x) (getLocalMaxPos save)
| x :: l1', y :: l2' => NewLocalStack l1' l2' m (updateLocal save y (getVal m x) (getLocalMaxPos save) )
| _, _ => DeleteLocal m
end.

Reserved Notation " L -[ M1 , S1 ]=> M2 , S2" (at level 60).
Inductive stmt_eval : Stmt -> MemoryLayer -> MemoryLayer -> MemoryLayer -> MemoryLayer -> Prop :=
| st_skip : forall sigma save,
   ( skip )-[ sigma , save ]=> sigma , save
| st_secv : forall s1 s2 sigma sigma1 sigma2 save save',
   ( s1 )-[ sigma , save ]=> sigma1 , save ->
   ( s2 )-[ sigma1 , save ]=> sigma2 , save' ->
   ( s1 ;; s2 )-[ sigma , save ]=> sigma2 , save'
| st_int : forall s a val sigma sigma1 save,
    val =A[ sigma ]A> a ->
    sigma1 = updateLocal sigma s a (getLocalMaxPos sigma) ->
    ( int' s <-- val )-[ sigma , save ]=> sigma1 , save
| st_bool : forall s b val sigma sigma1 save,
    val =B[ sigma ]B> b ->
    sigma1 = updateLocal sigma s b (getLocalMaxPos sigma) ->
    ( bool' s <-- val)-[ sigma , save ]=> sigma1 , save
| st_string : forall s val sigma sigma1 str save,
    val =S[ sigma ]S> str ->
    sigma1 = updateLocal sigma s str (getLocalMaxPos sigma) ->
    ( string' s <-- val )-[ sigma , save ]=> sigma1 , save
| st_asigint : forall s a val sigma sigma1 save,
    EqForTypes (getVal sigma s) (nrType 0) = true ->
    val =A[ sigma ]A> a ->
    sigma1 = updateAtAdress sigma (isLocal sigma s) (getAdress sigma s) a ->
    ( s :N= val )-[ sigma , save ]=> sigma1 , save
| st_asigbool : forall s b val sigma sigma1 save,
    EqForTypes (getVal sigma s) (boolType false) = true ->
    val =B[ sigma ]B> b ->
    sigma1 = updateAtAdress sigma (isLocal sigma s) (getAdress sigma s) b ->
    ( s :B= val )-[ sigma , save ]=> sigma1 , save
| st_asigstring : forall s val sigma sigma1 str save,
    EqForTypes (getVal sigma s) (strType str("") ) = true ->
    val =S[ sigma ]S> str ->
    sigma1 = updateAtAdress sigma (isLocal sigma s) (getAdress sigma s) str  ->
    ( s :S= val )-[ sigma , save ]=> sigma1 , save
| st_iffalse : forall b s1 sigma save,
    b =B[ sigma ]B> false ->
    ( ifthen b s1 )-[ sigma , save ]=> sigma , save
| st_iftrue : forall b s1 sigma sigma1 save,
    b =B[ sigma ]B> true ->
    ( s1 )-[ sigma , save ]=> sigma1 , save ->
    ( ifthen b s1 )-[ sigma , save ]=> sigma1 , save
| st_ifelsefalse : forall b s1 s2 sigma sigma2 save,
    b =B[ sigma ]B> false ->
    ( s2 )-[ sigma , save ]=> sigma2 , save ->
    ( ifthenelse b s1 s2 )-[ sigma , save ]=> sigma2 , save
| st_ifelsetrue : forall b s1 s2 sigma sigma1 save,
    b =B[ sigma ]B> true ->
    ( s1 )-[ sigma , save ]=> sigma1 , save ->
    ( ifthenelse b s1 s2 )-[ sigma , save ]=> sigma1 , save
| st_whilefalse : forall b s sigma save,
    b =B[ sigma ]B> false ->
    ( whileloop b s )-[ sigma , save ]=> sigma , save
| st_whiletrue : forall b s sigma sigma1 save,
    b =B[ sigma ]B> true ->
    ( s ;; whileloop b s )-[ sigma , save ]=> sigma1 , save ->
    ( whileloop b s )-[ sigma , save]=> sigma1 , save
| st_forloop_false : forall a b st s1 sigma sigma1 save,
    ( a )-[ sigma, save]=> sigma1, save ->
    b =B[ sigma1 ]B> false ->
    ( forloop a b st s1 )-[ sigma , save ]=> sigma1 , save
| st_forloop_true : forall a b st s1 sigma sigma1 sigma2 save,
    ( a )-[ sigma , save]=> sigma1,save ->
    (whileloop b (s1 ;; st) )-[ sigma1 , save ]=> sigma2 , save ->
    ( forloop a b st s1 )-[ sigma , save ]=> sigma2 , save
| st_intpoint : forall V P sigma sigma1 isl save,
    EqForTypes (getVal sigma P) (nrType 0) = true ->
    isl = isLocal sigma P ->
    sigma1 = updateLocal sigma V (pointer (getAdress sigma P) isl) (getLocalMaxPos sigma) ->
    ( int** V <-- P )-[ sigma , save]=> sigma1, save
| st_boolpoint : forall V P sigma sigma1 isl save,
    EqForTypes (getVal sigma P) (boolType false) = true ->
    isl = isLocal sigma P ->
    sigma1 = updateLocal sigma V (pointer (getAdress sigma P) isl) (getLocalMaxPos sigma) ->
    ( bool** V <-- P )-[ sigma , save]=> sigma1 , save
| st_strpoint : forall V P sigma sigma1 isl save,
    EqForTypes (getVal sigma P) (strType str("") ) = true ->
    isl = isLocal sigma P -> 
    sigma1 = updateLocal sigma V (pointer (getAdress sigma P) isl) (getLocalMaxPos sigma) ->
    ( string** V <-- P )-[ sigma , save]=> sigma1 , save
| st_intpoint_asig : forall V E i1 sigma sigma1 save,
    EqForTypes (getVal sigma V) (pointer 0 false) = true ->
    E =A[ sigma ]A> i1 ->
    sigma1 = updateAtAdress sigma (isPointerLocal (getVal sigma V) ) (getPointerAdress (getVal sigma V) ) i1  ->
    ( n* V ::= E )-[ sigma , save ]=> sigma1, save
| st_boolpoint_asig : forall V E i1 sigma sigma1 save,
    EqForTypes (getVal sigma V) (pointer 0 false) = true ->
    E =B[ sigma ]B> i1 ->
    sigma1 = updateAtAdress sigma (isPointerLocal (getVal sigma V) ) (getPointerAdress (getVal sigma V) ) i1 ->
   ( b* V ::= E )-[ sigma , save ]=> sigma1 , save
| st_strpoint_asig : forall V E i1 sigma sigma1 save,
    EqForTypes (getVal sigma V) (pointer 0 false) = true ->
    E =S[ sigma ]S> i1 ->
    sigma1 = updateAtAdress sigma (isPointerLocal (getVal sigma V) ) (getPointerAdress (getVal sigma V) ) i1  ->
   ( s* V ::= E )-[ sigma , save ]=> sigma1 , save
| st_switch : forall a cl sigma n v sigma' save,
    a =A[ sigma ]A> n ->
    v = (get_switch_case n cl) ->
    v -[ sigma , save]=> sigma' , save ->
    switch a cl -[ sigma , save ]=> sigma' , save
| st_dowhile_true : forall st b sigma sigma' sigma'' save,
    st -[ sigma , save ]=> sigma' , save ->
    b =B[ sigma' ]B> true ->
    ( whileloop b st ) -[ sigma' , save ]=> sigma'' , save ->
    do'{ st }while( b ) -[ sigma , save ]=> sigma' , save
| st_dowhile_false : forall st b sigma sigma' save,
    st -[ sigma , save ]=> sigma' , save ->
    b =B[ sigma' ]B> false ->
    do'{ st }while( b ) -[ sigma , save ]=> sigma' , save
| st_callfun : forall s L args stmt sigma sigma' sigma1 save,
    args = getArgs (getVal sigma s ) ->
    length L = length args ->
    sigma' = NewLocalStack L args sigma (DeleteLocal sigma)->
    stmt = getStmt (getVal sigma s ) ->
    ( stmt )-[ sigma' , sigma]=> sigma1 , save ->
    ( apelfunc s L )-[ sigma , save ]=> sigma1 , save
| st_return : forall sigma sigma' save save',
    save' = stack0 ->
    sigma' = MergeMemory save sigma->
    ( Return )-[sigma, save]=> sigma', save'
where "L -[ M1 , S1 ]=> M2 , S2" := (stmt_eval L M1 S1 M2 S2).

Example ex2 : exists stack', ( int' "x" <-- 10 ;;
                                int** "y" <-- "x" ;; 
                                n* "y" ::= 15 ) -[ stack0 , stack0 ]=> stack' , stack0
    /\ getVal stack' "x" = getPointerVal stack' "y".
Proof.
  eexists.
  split.
  *eapply st_secv.
  -eapply st_int. eapply e_const. unfold updateLocal. simpl. trivial.
  -eapply st_secv.
    --eapply st_intpoint.
    +simpl. trivial.
    +unfold updateLocal. simpl. trivial.
    +unfold updateLocal. simpl. trivial.
    --eapply st_intpoint_asig.
    +simpl. trivial.
    +eapply e_const.
    +unfold updateLocal. simpl. trivial.
  *simpl. unfold updateMemory. simpl. unfold getPointerVal. simpl. trivial.
Qed.

Example ex3 : exists stack', ( bool' "x" <--false ;; "x" :B= true )-[ stack0 , stack0 ]=> stack' , stack0
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
| l_funMain : forall stmt sigma sigma1 save,
  save = stack0 ->
  ( stmt )-[ sigma , save ]=> sigma1 , save->
  ( functiaMain stmt )-{ sigma }=> sigma1
| l_function : forall s L  stmt sigma sigma1,
  sigma1 = updateGlobal sigma s (code L stmt) (getGlobalMaxPos sigma) ->
  ( functie s L stmt )-{ sigma }=> sigma1
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
  eapply l_funMain. trivial. eapply st_skip.
  -split; simpl; unfold updateMemory; simpl; trivial.
Qed.

Definition sample1 := 
  int0' "x" ;' 
  void "fun" (("y")){
    "x" :N= "y" -' 100 ;;
    Return
  } ;'
  void main() {
     "x" :N= 135 ;;
     call "fun" (("x"))
  }.
Example ex5 : exists stack', ( sample1 )-{ stack0 }=> stack' 
      /\ getVal stack' "x" = 35.
Proof.
  eexists.  
  split.
  -unfold sample1. eapply l_secv.
    + eapply l_int0. unfold updateGlobal. simpl. trivial.
    + eapply l_secv.
      ++ eapply l_function. unfold updateGlobal. simpl. trivial.
      ++ eapply l_funMain. trivial.
        *eapply st_secv.
          **eapply st_asigint. simpl. trivial. 
            eapply e_const. unfold updateAtAdress. simpl. trivial.
          **eapply st_callfun; simpl; trivial.
            eapply st_secv.
            --eapply st_asigint; eauto.
              eapply e_sub. eapply e_var. eapply e_const. eauto.
            --eapply st_return; eauto.
   -simpl. unfold updateMemory. simpl. trivial.
Qed.

Example ex6 : exists stack', 
              (
                int' "x" <-- 0 ;;
                do'{
                   "x" :N= "x" +' 2
                }while("x" <' 0)
              )-[ stack0 , stack0 ]=> stack' , stack0
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
    +eapply l_funMain. trivial. eapply st_secv.
      *eapply st_asigint. simpl. trivial. eapply e_const. unfold updateAtAdress. simpl. trivial.
      *eapply st_switch. eapply e_var. simpl. trivial.
      eapply st_asigint. trivial. eapply e_const. trivial.
  -simpl. unfold updateMemory. simpl. reflexivity.
Qed.
  


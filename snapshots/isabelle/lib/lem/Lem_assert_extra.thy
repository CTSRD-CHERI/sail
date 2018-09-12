chapter \<open>Generated by Lem from \<open>assert_extra.lem\<close>.\<close>

theory "Lem_assert_extra" 

imports
  Main
  "Lem"

begin 


(*open import {ocaml} `Xstring`*)
(*open import {hol} `stringTheory` `lemTheory`*)
(*open import {coq} `Coq.Strings.Ascii` `Coq.Strings.String`*)
(*open import {isabelle} `$LIB_DIR/Lem`*)

(* ------------------------------------ *)
(* failing with a proper error message  *)
(* ------------------------------------ *)

(*val failwith: forall 'a. string -> 'a*)

(* ------------------------------------ *)
(* failing without an error message     *)
(* ------------------------------------ *)

(*val fail : forall 'a. 'a*)
definition fail  :: " 'a "  where 
     " fail = ( failwith (''fail''))"


(* ------------------------------------- *)
(* assertions                            *)
(* ------------------------------------- *)

(*val ensure : bool -> string -> unit*)
definition ensure  :: " bool \<Rightarrow> string \<Rightarrow> unit "  where 
     " ensure test msg = (
  if test then
    () 
  else
    failwith msg )"


end

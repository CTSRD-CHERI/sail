(*Generated by Lem from error.lem.*)
open Lem_list
open Lem_num
open Lem_string

open Show

(** [error] is a type used to represent potentially failing computations. [Success]
  * marks a successful completion of a computation, whilst [Fail err] marks a failure,
  * with [err] as the reason.
  *)
type 'a error
	= Success of 'a
	| Fail of string

(** [return] is the monadic lifting function for [error], representing a successful
  * computation.
  *)
(*val return : forall 'a. 'a -> error 'a*)
let return r = (Success r)

(** [fail err] represents a failing computation, with error message [err].
  *)
(*val fail : forall 'a. string -> error 'a*)
let fail err = (Fail err)

(** [(>>=)] is the monadic binding function for [error].
  *)
(*val >>= : forall 'a 'b. error 'a -> ('a -> error 'b) -> error 'b*)
let (>>=) x f =	
((match x with
		| Success s -> f s
		| Fail err  -> Fail err
	))

(** [repeatM count action] fails if [action] is a failing computation, or
  * successfully produces a list [count] elements long, where each element is
  * the value successfully returned by [action].
  *)
(*val repeatM : forall 'a. nat -> error 'a -> error (list 'a)*)
let rec repeatM count action =	
((match count with
		| 0 -> return []
		| m ->
				action >>= (fun head ->
				repeatM ( Nat_num.nat_monus m( 1)) action >>= (fun tail ->
				return (head::tail)))
	))

(** [repeatM' count seed action] is a variant of [repeatM] that acts like [repeatM]
  * apart from any successful result returns a tuple whose second component is [seed]
  * and whose first component is the same as would be returned by [repeatM].
  *)
(*val repeatM' : forall 'a 'b. nat -> 'b -> ('b -> error ('a * 'b)) -> error ((list 'a) * 'b)*)
let rec repeatM' count seed action =	
((match count with
		| 0 -> return ([], seed)
		| m ->
				action seed >>= (fun (head, seed) ->
				repeatM' ( Nat_num.nat_monus m( 1)) seed action >>= (fun (tail, seed) ->
				return ((head::tail), seed)))
	))
	
(** [mapM f xs] maps [f] across [xs], failing if [f] fails on any element of [xs].
  *)
(*val mapM : forall 'a 'b. ('a -> error 'b) -> list 'a -> error (list 'b)*)
let rec mapM f xs =	
((match xs with
		| []    -> return []
		| x::xs ->
				f x >>= (fun hd ->
				mapM f xs >>= (fun tl ->
				return (hd::tl)))
	))

(** [string_of_error err] produces a string representation of [err].
  *)
(*val string_of_error : forall 'a. Show 'a => error 'a -> string*)
let string_of_error dict_Show_Show_a e =	
((match e with
		| Fail err -> "Fail: " ^ err
		| Success s -> dict_Show_Show_a.show_method s
	))

let instance_Show_Show_Error_error_dict dict_Show_Show_a =({

  show_method = 
  (string_of_error dict_Show_Show_a)})
(*Generated by Lem from map_extra.lem.*)


open Lem_bool
open Lem_basic_classes
open Lem_function
open Lem_assert_extra
open Lem_maybe
open Lem_list
open Lem_num
open Lem_set
open Lem_map

(* -------------------------------------------------------------------------- *)
(* find                                                                       *)
(* -------------------------------------------------------------------------- *)

(*val find : forall 'k 'v. MapKeyType 'k => 'k -> map 'k 'v -> 'v*)
(*let find k m = match (lookup k m) with Just x -> x | Nothing -> failwith "Map_extra.find" end*)



(* -------------------------------------------------------------------------- *)
(* from sets / domain / range                                                 *)
(* -------------------------------------------------------------------------- *)


(*val fromSet : forall 'k 'v. MapKeyType 'k => ('k -> 'v) -> set 'k -> map 'k 'v*)
(*let fromSet f s = Set_helpers.fold (fun k m -> Map.insert k (f k) m) s Map.empty*)


(* -------------------------------------------------------------------------- *)
(* fold                                                                       *)
(* -------------------------------------------------------------------------- *)

(*val fold : forall 'k 'v 'r. MapKeyType 'k, SetType 'k, SetType 'v => ('k -> 'v -> 'r -> 'r) -> map 'k 'v -> 'r -> 'r*)
(*let fold f m v = Set_helpers.fold (fun (k, v) r -> f k v r) (Map.toSet m) v*)


(*val toList: forall 'k 'v. MapKeyType 'k => map 'k 'v -> list ('k * 'v)*)


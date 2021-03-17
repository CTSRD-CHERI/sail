Require Import Sail.Base.
Require Import String.
Require Import List.
Require Import Lia.
Import List.ListNotations.
Open Scope Z.

Definition MEMr {regval a e} (addr : mword a) size `{ArithFact (size >=? 0)}            : monad regval (mword (8 * size)) e := read_mem Read_plain a addr size.
Definition MEMr_reserve {regval a e} (addr : mword a) size `{ArithFact (size >=? 0)}    : monad regval (mword (8 * size)) e := read_mem Read_reserve a addr size.
Definition MEM_sync {rv e} (_:unit) : monad rv unit e := barrier (Barrier_MIPS_SYNC tt).

Definition MEMr_tagged {rv a e} (addr : mword a) size (allowTag : bool) `{ArithFact (size >? 0)} : monad rv (bool * mword (size * 8)) e :=
  (if allowTag then
    read_memt Read_plain addr size
  else
    (read_mem Read_plain a addr size >>= fun v => returnm (v, B0))) >>= fun '(v, t) =>
  maybe_fail "bool_of_bitU" (bool_of_bitU t) >>= fun t =>
  returnm (t, v).

Definition MEMr_tagged_reserve {rv a e} (addr : mword a) size (allowTag : bool) `{ArithFact (size >? 0)} : monad rv (bool * mword (size * 8)) e :=
  (if allowTag then
     read_memt Read_plain addr size
   else
     (read_mem Read_plain a addr size >>= fun v => returnm (v, B0))) >>= fun '(v, t) =>
  maybe_fail "bool_of_bitU" (bool_of_bitU t) >>= fun t =>
  returnm (t, v).

Definition MEMea {regval a e} (addr : mword a) size                : monad regval unit e := write_mem_ea Write_plain a addr size.
Definition MEMea_conditional {regval a e} (addr : mword a) size    : monad regval unit e := write_mem_ea Write_conditional a addr size.

Definition MEMval {regval a e} (addr : mword a) (size : Z) (v : mword (8 * size))                      : monad regval unit e := write_mem Write_plain a addr size v >>= fun _ => returnm tt.
Definition MEMval_conditional {regval a e} (addr : mword a) (size : Z) (v : mword (8 * size))          : monad regval bool e := write_mem Write_conditional a addr size v.

Definition MEMval_tagged {rv a e} (addr : mword a) size t (v : mword (size * 8)) : monad rv unit e            := write_memt Write_plain addr size v (bitU_of_bool t) >>= fun _ => returnm tt.
Definition MEMval_tagged_conditional {rv a e} (addr : mword a) size t (v : mword (size * 8)) :monad rv bool e := write_memt Write_conditional addr size v (bitU_of_bool t).

Definition MEMw_tagged {rv a e} (addr : mword a) size t (v : mword (size * 8)) : monad rv unit e := MEMea addr size             >> MEMval_tagged addr size t v.
Definition MEMw_tagged_conditional {rv a e} (addr : mword a) size t (v : mword (size * 8)) : monad rv bool e := MEMea_conditional addr size >> MEMval_tagged_conditional addr size t v.

(* Some wrappers copied from aarch64_extras *)
(* TODO: Harmonise into a common library *)
(*
Definition get_slice_int_bl len n lo :=
  (* TODO: Is this the intended behaviour? *)
  let hi := lo + len - 1 in
  let bs := bools_of_int (hi + 1) n in
  subrange_list false bs hi lo

val get_slice_int : forall 'a. Bitvector 'a => integer -> integer -> integer -> 'a
Definition get_slice_int len n lo := of_bools (get_slice_int_bl len n lo)
*)
Definition write_ram {rv e} m size (_ : mword m) (addr : mword m) (data : mword (8 * size)) : monad rv unit e :=
  MEMea addr size >>
  MEMval addr size data.

Definition read_ram {rv e} m size `{ArithFact (size >=? 0)} (_ : mword m) (addr : mword m) : monad rv (mword (8 * size)) e := MEMr addr size.
(*
Definition string_of_bits bs := string_of_bv (bits_of bs).
Definition string_of_int := show

Definition _sign_extend bits len := maybe_failwith (of_bits (exts_bv len bits))
Definition _zero_extend bits len := maybe_failwith (of_bits (extz_bv len bits))
*)
Definition shift_bits_left {rv e a b} (v : mword a) (n : mword b) : monad rv (mword a) e :=
  maybe_fail "shift_bits_left" (unsigned n) >>= fun n =>
  returnm (shiftl v n).

Definition shift_bits_right {rv e a b} (v : mword a) (n : mword b) : monad rv (mword a) e :=
  maybe_fail "shift_bits_right" (unsigned n) >>= fun n =>
  returnm (shiftr v n).

Definition shift_bits_right_arith {rv e a b} (v : mword a) (n : mword b) : monad rv (mword a) e :=
  maybe_fail "shift_bits_right" (unsigned n) >>= fun n =>
  returnm (arith_shiftr v n).

(* Use constants for undefined values for now *)
Definition internal_pick {rv a e} (vs : list a) : monad rv a e :=
match vs with
| (h::_) => returnm h
| _ => Fail "empty list in internal_pick"
end.
Definition undefined_string {rv e} (_:unit) : monad rv string e := returnm ""%string.
Definition undefined_unit {rv e} (_:unit) : monad rv unit e := returnm tt.
Definition undefined_int {rv e} (_:unit) : monad rv Z e := returnm (0:ii).
(*val undefined_vector : forall 'rv 'a 'e. integer -> 'a -> monad 'rv (list 'a) 'e*)
Definition undefined_vector {rv a e} len (u : a) `{ArithFact (len >=? 0)} : monad rv (vec a len) e := returnm (vec_init u len).
(*val undefined_bitvector : forall 'rv 'a 'e. Bitvector 'a => integer -> monad 'rv 'a 'e*)
Definition undefined_bitvector {rv e} len `{ArithFact (len >=? 0)} : monad rv (mword len) e := returnm (mword_of_int 0).
(*val undefined_bits : forall 'rv 'a 'e. Bitvector 'a => integer -> monad 'rv 'a 'e*)
Definition undefined_bits {rv e} := @undefined_bitvector rv e.
Definition undefined_bit {rv e} (_:unit) : monad rv bitU e := returnm BU.
(*Definition undefined_real {rv e} (_:unit) : monad rv real e := returnm (realFromFrac 0 1).*)
Definition undefined_range {rv e} i j `{ArithFact (i <=? j)} : monad rv {z : Z & ArithFact (i <=? z <=? j)} e := returnm (build_ex i).
Definition undefined_atom {rv e} i : monad rv Z e := returnm i.
Definition undefined_nat {rv e} (_:unit) : monad rv Z e := returnm (0:ii).

Definition skip {rv e} (_:unit) : monad rv unit e := returnm tt.

(*val elf_entry : unit -> integer*)
Definition elf_entry (_:unit) : Z := 0.
(*declare ocaml target_rep function elf_entry := `Elf_loader.elf_entry`*)

(*Definition print_bits msg bs := prerr_endline (msg ^ (string_of_bits bs))

val get_time_ns : unit -> integer*)
Definition get_time_ns (_:unit) : Z := 0.
(*declare ocaml target_rep function get_time_ns := `(fun () -> Big_int.of_int (int_of_float (1e9 *. Unix.gettimeofday ())))`*)

Definition eq_bit (x : bitU) (y : bitU) : bool :=
  match x, y with
  | B0, B0 => true
  | B1, B1 => true
  | BU, BU => true
  | _,_ => false
  end.

Require Import Zeuclid.
Definition euclid_modulo (m n : Z) `{ArithFact (n >? 0)} : {z : Z & ArithFact (0 <=? z <=? n-1)}.
refine (existT _ (ZEuclid.modulo m n) _).
constructor.
destruct H.
unbool_comparisons; unbool_comparisons_goal.
assert (Z.abs n = n). { rewrite Z.abs_eq; auto with zarith. }
rewrite <- H at 3.
lapply (ZEuclid.mod_always_pos m n); lia.
Qed.

(* Override the more general version *)

Definition mults_vec {n} (l : mword n) (r : mword n) : mword (2 * n) := mults_vec l r.
Definition mult_vec {n} (l : mword n) (r : mword n) : mword (2 * n) := mult_vec l r.


Definition print_endline (_:string) : unit := tt.
Definition prerr_endline (_:string) : unit := tt.
Definition prerr_string (_:string) : unit := tt.
Definition putchar {T} (_:T) : unit := tt.
Require DecimalString.
Definition string_of_int z := DecimalString.NilZero.string_of_int (Z.to_int z).

Lemma __MIPS_read_lemma : forall width, 8 * width = 8 * (8 * width ÷ 8).
intros.
rewrite Z.mul_comm.
rewrite Z.quot_mul; auto with zarith.
Qed.
Hint Resolve __MIPS_read_lemma : sail.

Lemma MEMr_wrapper_lemma : forall size : Z, 8 * size = 8 * (8 * (8 * size ÷ 8) ÷ 8).
intros.
rewrite Z.mul_comm.
rewrite Z.quot_mul; auto with zarith.
rewrite Z.mul_comm with (m := size).
rewrite Z.quot_mul; auto with zarith.
Qed.
Hint Resolve MEMr_wrapper_lemma : sail.

Lemma getCapOffset_lemma {x0 x1 x2 x : Z} :
 0 <= x0 <= 18446744073709551616 - 1 ->
 0 <= x1 <= 18446744073709551616 - 1 ->
 18446744073709551616 <= x2 <= 18446744073709551616 ->
 x = ZEuclid.modulo (x0 - x1) x2 ->
 0 <= x <= 18446744073709551616 - 1.
intros.
match goal with H:context [ZEuclid.modulo ?X ?Y] |- _ => pose proof (ZEuclid.mod_always_pos X Y) end.
lia.
Qed.
Hint Resolve getCapOffset_lemma : sail.


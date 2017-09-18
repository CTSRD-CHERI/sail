(*Generated by Lem from gnu_extensions/gnu_ext_program_header_table.lem.*)
(** [gnu_ext_program_header_table] contains GNU extension specific functionality
  * related to the program header table.
  *)

open Lem_basic_classes
open Lem_num

(** GNU extensions, as defined in the LSB, see section 11.2. *)

(** The element specifies the location and size of a segment that may be made
  * read-only after relocations have been processed.
  *)
let elf_pt_gnu_relro : Nat_big_num.num=  (Nat_big_num.add ( Nat_big_num.mul(Nat_big_num.of_int 4)(Nat_big_num.of_int 421345620))(Nat_big_num.of_int 2)) (* 0x6474e552 *)
(** The [p_flags] member specifies the permissions of the segment containing the
  * stack and is used to indicate whether the stack should be executable.
  *)
let elf_pt_gnu_stack : Nat_big_num.num=  (Nat_big_num.add ( Nat_big_num.mul(Nat_big_num.of_int 4)(Nat_big_num.of_int 421345620))(Nat_big_num.of_int 1)) (* 0x6474e551 *)
(** Element specifies the location and size of exception handling information. *)
let elf_pt_gnu_eh_frame : Nat_big_num.num=  (Nat_big_num.mul(Nat_big_num.of_int 4)(Nat_big_num.of_int 421345620))    (* 0x6474e550 *)

(** [string_of_gnu_ext_segment_type m] produces a string representation of
  * GNU extension segment type [m].
  *)
(*val string_of_gnu_ext_segment_type : natural -> string*)
let string_of_gnu_ext_segment_type pt:string=  
 (if Nat_big_num.equal pt elf_pt_gnu_relro then
    "GNU_RELRO"
  else if Nat_big_num.equal pt elf_pt_gnu_stack then
    "GNU_STACK"
  else if Nat_big_num.equal pt elf_pt_gnu_eh_frame then
    "GNU_EH_FRAME"
  else
    "Invalid GNU EXT segment type")

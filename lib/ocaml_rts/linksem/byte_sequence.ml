(*Generated by Lem from byte_sequence.lem.*)
(** [byte_sequence.lem], a list of bytes used for ELF I/O and other basic tasks
  * in the ELF model.
  *)

open Lem_basic_classes
open Lem_bool
open Lem_list
open Lem_num
open Lem_string
open Lem_assert_extra

open Error
open Missing_pervasives
open Show

(** A [byte_sequence], [bs], denotes a consecutive list of bytes.  Can be read
  * from or written to a binary file.  Most basic type in the ELF formalisation.
  *)
type byte_sequence =
  Sequence of ( char list)

(** [byte_list_of_byte_sequence bs] obtains the underlying list of bytes of the
  * byte sequence [bs].
  *)
(*val byte_list_of_byte_sequence : byte_sequence -> list byte*)
let byte_list_of_byte_sequence bs0:(char)list=  
 ((match bs0 with
    | Sequence xs -> xs
  ))

(** [compare_byte_sequence bs1 bs2] is an ordering comparison function for byte
  * sequences, suitable for constructing sets, maps and other ordered types
  * with.
  *)
(*val compare_byte_sequence : byte_sequence -> byte_sequence -> ordering*)
let compare_byte_sequence s1 s2:int=   
(lexicographic_compare compare_byte (byte_list_of_byte_sequence s1) (byte_list_of_byte_sequence s2))

let instance_Basic_classes_Ord_Byte_sequence_byte_sequence_dict:(byte_sequence)ord_class= ({

  compare_method = compare_byte_sequence;

  isLess_method = (fun f1 -> (fun f2 -> ( Lem.orderingEqual(compare_byte_sequence f1 f2) (-1))));

  isLessEqual_method = (fun f1 -> (fun f2 -> let result = (compare_byte_sequence f1 f2) in Lem.orderingEqual result (-1) || Lem.orderingEqual result 0));

  isGreater_method = (fun f1 -> (fun f2 -> ( Lem.orderingEqual(compare_byte_sequence f1 f2) 1)));

  isGreaterEqual_method = (fun f1 -> (fun f2 -> let result = (compare_byte_sequence f1 f2) in Lem.orderingEqual result 1 || Lem.orderingEqual result 0))})

(** [acquire_byte_list fname] exhaustively reads in a list of bytes from a file
  * pointed to by filename [fname].  Fails if the file does not exist, or if the
  * transcription otherwise fails.  Implemented as a primitive in OCaml.
  *)
(*val acquire_byte_list : string -> error (list byte)*)

(** [acquire fname] exhaustively reads in a byte_sequence from a file pointed to
  * by filename [fname].  Fails if the file does not exist, or if the transcription
  * otherwise fails.
  *)
(*val acquire : string -> error byte_sequence*)
let acquire fname1:(byte_sequence)error=  
 (Byte_sequence_wrapper.acquire_char_list fname1 >>= (fun bs ->
  return (Sequence bs)))

(** [serialise_byte_list fname bs] writes a list of bytes, [bs], to a binary file
  * pointed to by filename [fname].  Fails if the transcription fails.  Implemented
  * as a primitive in OCaml.
  *)
(*val serialise_byte_list : string -> list byte -> error unit*)

(** [serialise fname bs0] writes a byte sequence, [bs0], to a binary file pointed
  * to by filename [fname].  Fails if the transcription fails.
  *)
(*val serialise : string -> byte_sequence -> error unit*)
let serialise fname1 ss:(unit)error=  
 ((match ss with
    | Sequence ts -> Byte_sequence_wrapper.serialise_char_list fname1 ts
  ))

(** [empty], the empty byte sequence.
  *)
(*val empty : byte_sequence*)
let empty:byte_sequence=  (Sequence [])

(** [read_char bs0] reads a single byte from byte sequence [bs0] and returns the
  * remainder of the byte sequence.  Fails if [bs0] is empty.
  * TODO: rename to read_byte, probably.
  *)
(*val read_char : byte_sequence -> error (byte * byte_sequence)*)
let read_char (Sequence ts):(char*byte_sequence)error=  
 ((match ts with
    | []    -> fail "read_char: sequence is empty"
    | x::xs -> return (x, Sequence xs)
  ))

(** [repeat cnt b] creates a list of length [cnt] containing only [b].
  * TODO: move into missing_pervasives.lem.
  *)
(*val repeat' : natural -> byte -> list byte -> list byte*)
let rec repeat' count c acc:(char)list= 
  (
  if(Nat_big_num.equal count (Nat_big_num.of_int 0)) then acc else
    (repeat' ( Nat_big_num.sub_nat count (Nat_big_num.of_int 1)) c (c :: acc)))

(*val repeat : natural -> byte -> list byte*)
let repeat count c:(char)list=  (repeat' count c [])

(** [create cnt b] creates a byte sequence of length [cnt] containing only [b].
  *)
(*val create : natural -> byte -> byte_sequence*)
let create count c:byte_sequence=  
 (Sequence (repeat count c))

(** [zeros cnt] creates a byte sequence of length [cnt] containing only 0, the
  * null byte.
  *)
(*val zeros : natural -> byte_sequence*)
let zeros m:byte_sequence=  
 (create m '\000')

(** [length bs0] returns the length of [bs0].
  *)
(*val length : byte_sequence -> natural*)
let length0 (Sequence ts):Nat_big_num.num=  
 (Nat_big_num.of_int (List.length ts))


(** [concat bs] concatenates a list of byte sequences, [bs], into a single byte
  * sequence, maintaining byte order across the sequences.
  *)
(*val concat : list byte_sequence -> byte_sequence*)
let rec concat0 ts:byte_sequence=  
 ((match ts with
    | []                 -> Sequence []
    | ((Sequence x)::xs) ->
      (match concat0 xs with
        | Sequence tail -> Sequence ( List.rev_append (List.rev x) tail)
      )
  ))

(** [zero_pad_to_length len bs0] pads (on the right) consecutive zeros until the
  * resulting byte sequence is [len] long.  Returns [bs0] if [bs0] is already of
  * greater length than [len].
  *)
(*val zero_pad_to_length : natural -> byte_sequence -> byte_sequence*)
let zero_pad_to_length len bs:byte_sequence=  
  (let curlen = (length0 bs) in 
    if Nat_big_num.greater_equal curlen len then
      bs
    else
      concat0 [bs ; (zeros ( Nat_big_num.sub_nat len curlen))])

(** [from_byte_lists bs] concatenates a list of bytes [bs] and creates a byte
  * sequence from their contents.  Maintains byte order in [bs].
  *)
(*val from_byte_lists : list (list byte) -> byte_sequence*)
let from_byte_lists ts:byte_sequence=  
 (Sequence (List.concat ts))

(** [string_of_char_list cs] converts a list of characters into a string.
  * Implemented as a primitive in OCaml.
  *)
(*val string_of_char_list : list char -> string*)

(** [char_list_of_byte_list bs] converts byte list [bs] into a list of characters.
  * Implemented as a primitive in OCaml and Isabelle.
  * TODO: is this actually being used in the Isabelle backend?  All string functions
  * should be factored out by target-specific definitions.
  *)
(*val char_list_of_byte_list : list byte -> list char*)

(** [string_of_byte_sequence bs0] converts byte sequence [bs0] into a string
  * representation.
  *)
(*val string_of_byte_sequence : byte_sequence -> string*)
let string_of_byte_sequence (Sequence ts):string=  
 (let cs = ( ts) in
    Xstring.implode cs)

(** [equal bs0 bs1] checks whether two byte sequences, [bs0] and [bs1], are equal.
  *)
(*val equal : byte_sequence -> byte_sequence -> bool*)
let rec equal left right:bool=  
 ((match (left, right) with
    | (Sequence [], Sequence []) -> true
    | (Sequence (x::xs), Sequence (y::ys)) ->        
(x = y) && equal (Sequence xs) (Sequence ys)
    | (_, _) -> false
  ))

(** [dropbytes cnt bs0] drops [cnt] bytes from byte sequence [bs0].  Fails if
  * [cnt] is greater than the length of [bs0].
  *)
(*val dropbytes : natural -> byte_sequence -> error byte_sequence*)
let rec dropbytes count (Sequence ts):(byte_sequence)error=  
 (if Nat_big_num.equal count Nat_big_num.zero then
    return (Sequence ts)
  else
    (match ts with
      | []    -> fail "dropbytes: cannot drop more bytes than are contained in sequence"
      | x::xs -> dropbytes ( Nat_big_num.sub_nat count(Nat_big_num.of_int 1)) (Sequence xs)
    ))

(*val takebytes_r_with_length: nat -> natural -> byte_sequence -> error byte_sequence*)
let rec takebytes_r_with_length count ts_length (Sequence ts):(byte_sequence)error=  
  (if Nat_big_num.greater_equal ts_length (Nat_big_num.of_int count) then 
    return (Sequence (list_take_with_accum count [] ts))
  else
    fail "takebytes: cannot take more bytes than are contained in sequence")

(*val takebytes : natural -> byte_sequence -> error byte_sequence*)
let takebytes count (Sequence ts):(byte_sequence)error=  
 (let result = (takebytes_r_with_length (Nat_big_num.to_int count) (Missing_pervasives.length ts) (Sequence ts)) in 
    result)

(*val takebytes_with_length : natural -> natural -> byte_sequence -> error byte_sequence*)
let takebytes_with_length count ts_length (Sequence ts):(byte_sequence)error=  
( 
  (* let _ = Missing_pervasives.errs ("Trying to take " ^ (show count) ^ " bytes from sequence of " ^ (show (List.length ts)) ^ "\n") in *)let result = (takebytes_r_with_length (Nat_big_num.to_int count) ts_length (Sequence ts)) in 
  (*let _ = Missing_pervasives.errs ("Succeeded\n") in *)
    result)

(** [read_2_bytes_le bs0] reads two bytes from [bs0], returning them in
  * little-endian order, and returns the remainder of [bs0].  Fails if [bs0] has
  * length less than 2.
  *)
(*val read_2_bytes_le : byte_sequence -> error ((byte * byte) * byte_sequence)*)
let read_2_bytes_le bs0:((char*char)*byte_sequence)error=  
 (read_char bs0 >>= (fun (b0, bs1) ->
  read_char bs1 >>= (fun (b1, bs2) ->
  return ((b1, b0), bs2))))

(** [read_2_bytes_be bs0] reads two bytes from [bs0], returning them in
  * big-endian order, and returns the remainder of [bs0].  Fails if [bs0] has
  * length less than 2.
  *)
(*val read_2_bytes_be : byte_sequence -> error ((byte * byte) * byte_sequence)*)
let read_2_bytes_be bs0:((char*char)*byte_sequence)error=  
 (read_char bs0 >>= (fun (b0, bs1) ->
  read_char bs1 >>= (fun (b1, bs2) ->
  return ((b0, b1), bs2))))

(** [read_4_bytes_le bs0] reads four bytes from [bs0], returning them in
  * little-endian order, and returns the remainder of [bs0].  Fails if [bs0] has
  * length less than 4.
  *)
(*val read_4_bytes_le : byte_sequence -> error ((byte * byte * byte * byte) * byte_sequence)*)
let read_4_bytes_le bs0:((char*char*char*char)*byte_sequence)error=  
 (read_char bs0 >>= (fun (b0, bs1) ->
  read_char bs1 >>= (fun (b1, bs2) ->
  read_char bs2 >>= (fun (b2, bs3) ->
  read_char bs3 >>= (fun (b3, bs4) ->
  return ((b3, b2, b1, b0), bs4))))))

(** [read_4_bytes_be bs0] reads four bytes from [bs0], returning them in
  * big-endian order, and returns the remainder of [bs0].  Fails if [bs0] has
  * length less than 4.
  *)
(*val read_4_bytes_be : byte_sequence -> error ((byte * byte * byte * byte) * byte_sequence)*)
let read_4_bytes_be bs0:((char*char*char*char)*byte_sequence)error=  
 (read_char bs0 >>= (fun (b0, bs1) ->
  read_char bs1 >>= (fun (b1, bs2) ->
  read_char bs2 >>= (fun (b2, bs3) ->
  read_char bs3 >>= (fun (b3, bs4) ->
  return ((b0, b1, b2, b3), bs4))))))

(** [read_8_bytes_le bs0] reads eight bytes from [bs0], returning them in
  * little-endian order, and returns the remainder of [bs0].  Fails if [bs0] has
  * length less than 8.
  *)
(*val read_8_bytes_le : byte_sequence -> error ((byte * byte * byte * byte * byte * byte * byte * byte) * byte_sequence)*)
let read_8_bytes_le bs0:((char*char*char*char*char*char*char*char)*byte_sequence)error=  
 (read_char bs0 >>= (fun (b0, bs1) ->
  read_char bs1 >>= (fun (b1, bs2) ->
  read_char bs2 >>= (fun (b2, bs3) ->
  read_char bs3 >>= (fun (b3, bs4) ->
  read_char bs4 >>= (fun (b4, bs5) ->
  read_char bs5 >>= (fun (b5, bs6) ->
  read_char bs6 >>= (fun (b6, bs7) ->
  read_char bs7 >>= (fun (b7, bs8) ->
  return ((b7, b6, b5, b4, b3, b2, b1, b0), bs8))))))))))

(** [read_8_bytes_be bs0] reads eight bytes from [bs0], returning them in
  * big-endian order, and returns the remainder of [bs0].  Fails if [bs0] has
  * length less than 8.
  *)
(*val read_8_bytes_be : byte_sequence -> error ((byte * byte * byte * byte * byte * byte * byte * byte) * byte_sequence)*)
let read_8_bytes_be bs0:((char*char*char*char*char*char*char*char)*byte_sequence)error=  
 (read_char bs0 >>= (fun (b0, bs1) ->
  read_char bs1 >>= (fun (b1, bs2) ->
  read_char bs2 >>= (fun (b2, bs3) ->
  read_char bs3 >>= (fun (b3, bs4) ->
  read_char bs4 >>= (fun (b4, bs5) ->
  read_char bs5 >>= (fun (b5, bs6) ->
  read_char bs6 >>= (fun (b6, bs7) ->
  read_char bs7 >>= (fun (b7, bs8) ->
  return ((b0, b1, b2, b3, b4, b5, b6, b7), bs8))))))))))

(** [partition pnt bs0] splits [bs0] into two parts at index [pnt].  Fails if
  * [pnt] is greater than the length of [bs0].
  *)
(*val partition : natural -> byte_sequence -> error (byte_sequence * byte_sequence)*)
let partition0 idx1 bs0:(byte_sequence*byte_sequence)error=  
 (takebytes idx1 bs0 >>= (fun l ->
  dropbytes idx1 bs0 >>= (fun r ->
  return (l, r))))

(*val partition_with_length : natural -> natural -> byte_sequence -> error (byte_sequence * byte_sequence)*)
let partition_with_length idx1 bs0_length bs0:(byte_sequence*byte_sequence)error=  
 (takebytes_with_length idx1 bs0_length bs0 >>= (fun l ->
  dropbytes idx1 bs0 >>= (fun r ->
  return (l, r))))

(** [offset_and_cut off cut bs0] first cuts [off] bytes off [bs0], then cuts
  * the resulting byte sequence to length [cut].  Fails if [off] is greater than
  * the length of [bs0] and if [cut] is greater than the length of the intermediate
  * byte sequence.
  *)
(*val offset_and_cut : natural -> natural -> byte_sequence -> error byte_sequence*)
let offset_and_cut off cut bs0:(byte_sequence)error=  
 (dropbytes off bs0 >>= (fun bs1 ->
  takebytes cut bs1 >>= (fun res ->
  return res)))

let instance_Show_Show_Byte_sequence_byte_sequence_dict:(byte_sequence)show_class= ({

  show_method = string_of_byte_sequence})

let instance_Basic_classes_Eq_Byte_sequence_byte_sequence_dict:(byte_sequence)eq_class= ({

  isEqual_method = equal;

  isInequal_method = (fun l r->not (equal l r))})

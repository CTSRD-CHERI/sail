(*Generated by Lem from abis/mips64/abi_mips64.lem.*)
(** [abi_mips64] contains top-level definition for the MIPS64 ABI.
  *)

open Lem_basic_classes
open Lem_bool
open Lem_list
open Lem_num
open Lem_maybe
open Error
open Lem_map
open Lem_assert_extra

open Missing_pervasives
open Elf_header
open Elf_types_native_uint
open Elf_file
open Elf_interpreted_segment
open Elf_interpreted_section

open Endianness
open Memory_image
(* open import Elf_memory_image *)

open Abi_classes
(*open import Abi_mips64_relocation*)
open Abi_mips64_elf_header

(** [abi_mips64_compute_program_entry_point segs entry] computes the program
  * entry point using ABI-specific conventions.  On MIPS64 the entry point in
  * the ELF header ([entry] here) is the real entry point.  On other ABIs, e.g.
  * PowerPC64, the entry point [entry] is a pointer into one of the segments
  * constituting the process image (passed in as [segs] here for a uniform
  * interface).
  *)
(*val abi_mips64_compute_program_entry_point : list elf64_interpreted_segments -> elf64_addr -> error natural*)
let abi_mips64_compute_program_entry_point segs entry:(Nat_big_num.num)error=	
 (return (Ml_bindings.nat_big_num_of_uint64 entry))

(*val header_is_mips64 : elf64_header -> bool*)
let header_is_mips64 h:bool=    
   (is_valid_elf64_header h
    && ((Lem.option_equal (=) (Lem_list.list_index h.elf64_ident (Nat_big_num.to_int elf_ii_data)) (Some (Uint32.of_string (Nat_big_num.to_string elf_data_2msb))))
    && (is_valid_abi_mips64_machine_architecture (Nat_big_num.of_string (Uint32.to_string h.elf64_machine))
    && is_valid_abi_mips64_magic_number h.elf64_ident)))

type 'abifeature plt_entry_address_fn = Nat_big_num.num (* offset in PLT? *) -> 'abifeature annotated_memory_image (* img *) -> Nat_big_num.num (* addr *)

type 'abifeature mips64_abi_feature = 
    GOT1 of  ( (string * ( symbol_definition option))list)
    | PLT1 of ( (string * ( symbol_definition option) * 'abifeature plt_entry_address_fn)list)
    
(*val abiFeatureCompare : forall 'abifeature. mips64_abi_feature 'abifeature -> mips64_abi_feature 'abifeature -> Basic_classes.ordering*)
let abiFeatureCompare1 f1 f2:int=    
  ((match (f1, f2) with
        (GOT1(_), GOT1(_)) -> 0
        | (GOT1(_), PLT1(_)) -> (-1)
        | (PLT1(_), PLT1(_)) -> 0
        | (PLT1(_), GOT1(_)) -> 1
    ))

(*val abiFeatureTagEq : forall 'abifeature. mips64_abi_feature 'abifeature -> mips64_abi_feature 'abifeature -> bool*)
let abiFeatureTagEq1 f1 f2:bool=    
 ((match (f1, f2) with
        (GOT1(_), GOT1(_)) -> true
        | (PLT1(_), PLT1(_)) -> true
        | (_, _) -> false
    ))

let instance_Abi_classes_AbiFeatureTagEquiv_Abi_mips64_mips64_abi_feature_dict:('abifeature mips64_abi_feature)abiFeatureTagEquiv_class= ({

  abiFeatureTagEquiv_method = abiFeatureTagEq1})

let instance_Basic_classes_Ord_Abi_mips64_mips64_abi_feature_dict:('abifeature mips64_abi_feature)ord_class= ({

  compare_method = abiFeatureCompare1;

  isLess_method = (fun f1 -> (fun f2 -> ( Lem.orderingEqual(abiFeatureCompare1 f1 f2) (-1))));

  isLessEqual_method = (fun f1 -> (fun f2 -> Pset.mem (abiFeatureCompare1 f1 f2)(Pset.from_list compare [(-1); 0])));

  isGreater_method = (fun f1 -> (fun f2 -> ( Lem.orderingEqual(abiFeatureCompare1 f1 f2) 1)));

  isGreaterEqual_method = (fun f1 -> (fun f2 -> Pset.mem (abiFeatureCompare1 f1 f2)(Pset.from_list compare [1; 0])))})

(*val section_is_special : forall 'abifeature. elf64_interpreted_section -> annotated_memory_image 'abifeature -> bool*)
let section_is_special2 s img2:bool=    
  (elf_section_is_special s img2) 

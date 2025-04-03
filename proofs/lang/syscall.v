From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool seq eqtype ssralg.
From Coq Require Import PArith ZArith.
Require Import
  word
  type
  utils.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Unset Elimination Schemes.

Variant syscall_t : Type := 
  | RandomBytes of positive
  | Futex
  | Mmap
  | Mremap.

Scheme Equality for syscall_t.

Lemma syscall_t_eq_axiom : Equality.axiom syscall_t_beq.
Proof.
  exact:
    (eq_axiom_of_scheme internal_syscall_t_dec_bl internal_syscall_t_dec_lb).
Qed.

HB.instance Definition _ := hasDecEq.Build syscall_t syscall_t_eq_axiom.

(* -------------------------------------------------------------------- *)
(* For typing                                                           *)

(* Before stack alloc ie uprog *)

Record syscall_sig_t := {
  scs_tin  : seq stype;
  scs_tout : seq stype
}.

Definition syscall_num (o: syscall_t) : Z :=
  match o with
  | RandomBytes _ => 318
  | Futex => 202
  | Mmap => 9
  | Mremap => 25
  end.

Definition syscall_sig_u {pd: PointerData} (o : syscall_t) : syscall_sig_t := 
  match o with
  | RandomBytes len => {| scs_tin := [:: sarr len; sword Uptr]; scs_tout := [:: sarr len; sword Uptr] |}
  | Futex => {| scs_tin := [:: sword Uptr; sword Uptr; sword U32; sword Uptr; sword Uptr; sword U32]; scs_tout := [:: sword Uptr] |}
  | Mmap => {| scs_tin := [:: sword Uptr; sword Uptr; sword Uptr; sword Uptr; sword Uptr; sword Uptr]; scs_tout := [:: sword Uptr] |}
  | Mremap => {| scs_tin := [:: sword Uptr; sword Uptr; sword Uptr; sword Uptr; sword Uptr]; scs_tout := [:: sword Uptr] |}
  end.

(* After stack alloc ie sprog *)
Definition syscall_sig_s {pd:PointerData} (o:syscall_t) : syscall_sig_t := 
  match o with
  | RandomBytes _ => {| scs_tin := [:: sword Uptr; sword Uptr; sword Uptr; sword Uptr]; scs_tout := [::sword Uptr] |}
  | Futex => {| scs_tin := [:: sword Uptr; sword Uptr; sword Uptr; sword U32; sword Uptr; sword Uptr; sword U32]; scs_tout := [:: sword Uptr] |} 
  | Mmap => {| scs_tin := [:: sword Uptr; sword Uptr; sword Uptr; sword Uptr; sword Uptr; sword Uptr; sword Uptr]; scs_tout := [:: sword Uptr] |}
  | Mremap => {| scs_tin := [:: sword Uptr; sword Uptr; sword Uptr; sword Uptr; sword Uptr; sword Uptr]; scs_tout := [:: sword Uptr] |}
  end.


(* -------------------------------------------------------------------- *)
(* For the semantic                                                     *)
Class syscall_sem {pd : PointerData} (syscall_state : Type) := {
  get_random : syscall_state -> Z -> word Uptr -> syscall_state * (seq u8 * word Uptr);
  futex : syscall_state -> word Uptr -> word Uptr -> word U32 -> word Uptr -> word Uptr -> word U32 -> syscall_state * word Uptr;
  mmap : syscall_state -> word Uptr -> word Uptr -> word Uptr -> word Uptr -> word Uptr -> word Uptr -> syscall_state * word Uptr;
  mremap : syscall_state -> word Uptr -> word Uptr -> word Uptr -> word Uptr -> word Uptr -> syscall_state * word Uptr;
}.


Definition syscall_state_t {pd : PointerData} {syscall_state : Type} {sc_sem: syscall_sem syscall_state} := syscall_state.

(* * Jasmin semantics with “partial values”. *)

(* ** Imports and settings *)
From mathcomp Require Import all_ssreflect all_algebra.
Require Import ZArith Psatz.
Require Export utils syscall wsize word type low_memory sem_type values.
Import Utf8.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope Z_scope.




Section SourceSysCall.

Context
  {pd: PointerData}
  {syscall_state : Type}
  {sc_sem : syscall_sem syscall_state} .

Definition of_list {ws} (l:list (word ws)) (len: positive): WArray.array len :=
    let m := Mz.empty in
    let do8 (mz: Mz.t _ * Z) (w:u8) :=
      let '(m,z) := mz in
      (Mz.set m z w, Z.succ z) in
    let dow (mz: Mz.t _ * Z) (w:word ws) :=
      foldl do8 mz (LE.encode w) in
    let '(m, z) := foldl dow (Mz.empty u8, 0%Z) l in
    {| WArray.arr_data := m |}.

(** FIXME: sys_getrandom can fail **)
Definition exec_getrandom_u (scs : syscall_state) len vs :=
  Let: (a, f) :=
    match vs with
    | [:: array; flag] => 
        Let a := to_arr len array in
        Let f := to_word Uptr flag in
        ok (a, f)
    | _ => type_error
    end in
  let sd := get_random scs (Zpos len) f in
  let t := of_list sd.2.1 len in
  Let _ := assert (Z.of_nat (size sd.2.1) <=? Z.pos len)%Z ErrType in
  ok (sd.1, [::Varr t; Vword sd.2.2]).

Definition exec_futex_u (scs: syscall_state) (vs: seq value) := 
  Let: (u, f, v, t, u2, v3) :=
    match vs with
    | [:: uaddr; futex_op; val; timeout; uaddr2; val3] =>
        Let u := to_word Uptr uaddr in
        Let f := to_word Uptr futex_op in
        Let v := to_word U32 val in
        Let t := to_word Uptr timeout in
        Let u2 := to_word Uptr uaddr2 in
        Let v3 := to_word U32 val3 in
        ok (u, f, v, t, u2, v3)
    | _ => type_error
    end in
  let: (st, ret) := futex scs u f v t u2 v3 in
  ok (st, [:: Vword ret]).

Definition exec_mmap_u (scs: syscall_state) (vs: seq value) :=
  Let: (a, l, p, f, fd, o):=
    match vs with
    | [:: addr; len; prot; flags; fildes; off] =>
        Let a := to_word Uptr addr in
        Let l := to_word Uptr len in
        Let p := to_word Uptr prot in
        Let f := to_word Uptr flags in
        Let fd := to_word Uptr fildes in
        Let o := to_word Uptr off in
        ok (a, l, p, f, fd, o)
    | _ => type_error
    end in
  let: (st, ret) := mmap scs a l p f fd o in
  ok (st, [:: Vword ret]).

Definition exec_munmap_u (scs: syscall_state) (vs: seq value) :=
  Let: (a, l):=
    match vs with
    | [:: addr; len] =>
        Let a := to_word Uptr addr in
        Let l := to_word Uptr len in
        ok (a, l)
    | _ => type_error
    end in
  let: (st, ret) := munmap scs a l in
  ok (st, [:: Vword ret]).

Definition exec_mremap_u (scs: syscall_state) (vs: seq value) :=
  Let: (a, ol, nl, f, na):=
    match vs with
    | [:: addr; oldlen; newlen; flags; newaddr] =>
        Let a := to_word Uptr addr in
        Let ol := to_word Uptr oldlen in
        Let nl := to_word Uptr newlen in
        Let f := to_word Uptr flags in
        Let na := to_word Uptr newaddr in
        ok (a, ol, nl, f, na)
    | _ => type_error
    end in
  let: (st, ret) := mremap scs a ol nl f na in
  ok (st, [:: Vword ret]).

Definition exec_syscall_u
  (scs : syscall_state_t)
  (m : mem)
  (o : syscall_t)
  (vs : values) :
  exec (syscall_state_t * mem * values) :=
  match o with
  | RandomBytes len =>
      Let sv := exec_getrandom_u scs len vs in
      ok (sv.1, m, sv.2)
  | Futex => 
      Let sv := exec_futex_u scs vs in
      ok (sv.1, m, sv.2)
  | Mmap =>
      Let sv := exec_mmap_u scs vs in
      ok (sv.1, m, sv.2)
  | Munmap =>
      Let sv := exec_munmap_u scs vs in
      ok (sv.1, m, sv.2)
  | Mremap =>
      Let sv := exec_mremap_u scs vs in
      ok (sv.1, m, sv.2)
  end.

Lemma exec_syscallPu scs m o vargs vargs' rscs rm vres :
  exec_syscall_u scs m o vargs = ok (rscs, rm, vres) →
  List.Forall2 value_uincl vargs vargs' →
  exists2 vres' : values,
    exec_syscall_u scs m o vargs' = ok (rscs, rm, vres') & List.Forall2 value_uincl vres vres'.
Proof.
Admitted.
(*  rewrite /exec_syscall_u; case: o => [ p | _ ].
  t_xrbindP => -[scs' v'] /= h ??? hu; subst scs' m v'.
  move: h; rewrite /exec_getrandom_u.
  case: hu => // va va' ?? /of_value_uincl_te h [] //.
  t_xrbindP => a /h{h}[? /= -> ?] -> ??; subst rscs vres.
  by move => /=; eexists; eauto.
Qed. *)

Definition mem_equiv m1 m2 := stack_stable m1 m2 /\ validw m1 =2 validw m2.

Lemma exec_syscallSu scs m o vargs rscs rm vres :
  exec_syscall_u scs m o vargs = ok (rscs, rm, vres) →
  mem_equiv m rm.
Admitted.
(* rewrite /exec_syscall_u; case: o => [ p |  ].
  by t_xrbindP => -[scs' v'] /= _ _ <- _.
   Admitted. *)

End SourceSysCall.

Section Section.

Context {pd: PointerData} {syscall_state : Type} {sc_sem : syscall_sem syscall_state}.

Definition exec_getrandom_s_core (scs : syscall_state_t) (m : mem) (sys_num: pointer) (p:pointer) (len:pointer) (flag:pointer) : (exec (syscall_state_t * mem * sem_tuple (syscall_sig_s (RandomBytes 1)).(scs_tout))) := 
  Let _ := assert (Z.eqb (wunsigned sys_num) (syscall_num (RandomBytes 1))) ErrType in 
  let len := wunsigned len in
  let sd := syscall.get_random scs len flag in
  Let m := fill_mem m p sd.2.1 in
  ok (sd.1, m, sd.2.2).

Definition exec_futex_s_core (scs:syscall_state_t) (m:mem) (sys_num:pointer) (uaddr:pointer) (op:pointer) (val:word U32) (timeout:pointer) (addr2:pointer) (val3:word U32): (exec (syscall_state_t * mem * sem_tuple (syscall_sig_s Futex).(scs_tout))) :=
  Let _ := assert (Z.eqb (wunsigned sys_num) (syscall_num (Futex))) ErrType in 
  let '(st, ret) := syscall.futex scs uaddr op val timeout addr2 val3 in
  ok(st, m, ret).

Definition exec_mmap_s_core (scs:syscall_state_t) (m:mem) (sys_num:pointer) (addr:pointer) (len:pointer) (prot:pointer) (flags:pointer) (fildes:pointer) (off:pointer): (exec (syscall_state * mem * sem_tuple (syscall_sig_s Mmap).(scs_tout))) :=
  Let _ := assert (Z.eqb (wunsigned sys_num) (syscall_num (Mmap))) ErrType in 
  let '(st, ret) := syscall.mmap scs addr len prot flags fildes off in
  ok(st, m, ret).

Definition exec_munmap_s_core (scs:syscall_state_t) (m:mem) (sys_num:pointer) (addr:pointer) (len:pointer): (exec (syscall_state * mem * sem_tuple (syscall_sig_s Munmap).(scs_tout))) :=
  Let _ := assert (Z.eqb (wunsigned sys_num) (syscall_num (Munmap))) ErrType in 
  let '(st, ret) := syscall.munmap scs addr len in
  ok(st, m, ret).

Definition exec_mremap_s_core (scs:syscall_state_t) (m:mem) (sys_num:pointer) (addr:pointer) (oldlen:pointer) (newlen:pointer) (flags:pointer) (newaddr:pointer): (exec (syscall_state * mem * sem_tuple (syscall_sig_s Mremap).(scs_tout))) :=
  Let _ := assert (Z.eqb (wunsigned sys_num) (syscall_num (Mremap))) ErrType in 
  let '(st, ret) := syscall.mremap scs addr oldlen newlen flags newaddr in
  ok(st, m, ret).

Lemma exec_getrandom_s_core_stable scs m sys_num p len _fl rscs rm rp :
  exec_getrandom_s_core scs m sys_num p len _fl = ok (rscs, rm, rp) →
  stack_stable m rm.
Proof. by rewrite /exec_getrandom_s_core; t_xrbindP => _ rm' /fill_mem_stack_stable hf ? <- ?. Qed.

Lemma exec_getrandom_s_core_validw scs m sys_num p len _fl rscs rm rp : 
  exec_getrandom_s_core scs m sys_num p len _fl = ok (rscs, rm, rp) →
  validw m =2 validw rm.
Admitted.
(* Proof. by rewrite /exec_getrandom_s_core; t_xrbindP => _ rm' /fill_mem_validw_eq hf ? <- ?. Qed. *)

Definition sem_syscall (o:syscall_t) : 
     syscall_state_t -> mem -> sem_prod (syscall_sig_s o).(scs_tin) (exec (syscall_state_t * mem * sem_tuple (syscall_sig_s o).(scs_tout))) := 
  match o with
  | RandomBytes _ => exec_getrandom_s_core
  | Futex => exec_futex_s_core
  | Mmap => exec_mmap_s_core
  | Munmap => exec_munmap_s_core
  | Mremap => exec_mremap_s_core
  end.

Definition exec_syscall_s (scs : syscall_state_t) (m : mem) (o:syscall_t) vs : exec (syscall_state_t * mem * values) :=
  let semi := sem_syscall o in
  Let: (scs', m', t) := app_sopn _ (semi scs m) vs in
  ok (scs', m', list_ltuple t).
  
Lemma syscall_sig_s_noarr o : all is_not_sarr (syscall_sig_s o).(scs_tin).
Proof. by case: o. Qed.

Lemma exec_syscallPs_eq scs m o vargs vargs' rscs rm vres :
  exec_syscall_s scs m o vargs = ok (rscs, rm, vres) → 
  List.Forall2 value_uincl vargs vargs' → 
  exec_syscall_s scs m o vargs' = ok (rscs, rm, vres).
Proof.
  rewrite /exec_syscall_s; t_xrbindP => -[[scs' m'] t] happ [<- <- <-] hu.
  by have -> := vuincl_sopn (syscall_sig_s_noarr o ) hu happ.
Qed.
 
Lemma exec_syscallPs scs m o vargs vargs' rscs rm vres :
  exec_syscall_s scs m o vargs = ok (rscs, rm, vres) → 
  List.Forall2 value_uincl vargs vargs' → 
  exists2 vres' : values,
    exec_syscall_s scs m o vargs' = ok (rscs, rm, vres') & List.Forall2 value_uincl vres vres'.
Proof.
  move=> h1 h2; rewrite (exec_syscallPs_eq h1 h2).
  by exists vres=> //; apply List_Forall2_refl.
Qed.

Lemma sem_syscall_equiv o scs m : 
  mk_forall (fun (rm: (syscall_state_t * mem * _)) => mem_equiv m rm.1.2)
            (sem_syscall o scs m).
Admitted.
(*  case: o => _len /= sys_num p len _fl [[scs' rm] t] /= hex; split.
  + by apply: exec_getrandom_s_core_stable hex. 
  by apply: exec_getrandom_s_core_validw hex.
   Qed. *)

Lemma exec_syscallSs scs m o vargs rscs rm vres :
  exec_syscall_s scs m o vargs = ok (rscs, rm, vres) → 
  mem_equiv m rm.
Proof.
  rewrite /exec_syscall_s; t_xrbindP => -[[scs' m'] t] happ [_ <- _].
  apply (mk_forallP (sem_syscall_equiv o scs m) happ).
Qed.

End Section.

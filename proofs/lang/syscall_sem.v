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
  Let _ :=
    match vs with
    | [:: v] => to_arr len v
    | _ => type_error
    end in
  let sd := get_random scs (Zpos len) in
  let t := of_list sd.2 len in
  Let _ := assert (Z.of_nat (size sd.2) <=? Z.pos len)%Z ErrType in
  ok (sd.1, [::Varr t; Vword (wrepr Uptr (Z.of_nat (size sd.2)))]).

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
  end.

Lemma exec_syscallPu scs m o vargs vargs' rscs rm vres :
  exec_syscall_u scs m o vargs = ok (rscs, rm, vres) →
  List.Forall2 value_uincl vargs vargs' →
  exists2 vres' : values,
    exec_syscall_u scs m o vargs' = ok (rscs, rm, vres') & List.Forall2 value_uincl vres vres'.
Proof.
  rewrite /exec_syscall_u; case: o => [ p ].
  t_xrbindP => -[scs' v'] /= h ??? hu; subst scs' m v'.
  move: h; rewrite /exec_getrandom_u.
  case: hu => // va va' ?? /of_value_uincl_te h [] //.
  t_xrbindP => a /h{h}[? /= -> ?] -> ??; subst rscs vres.
  by move => /=; eexists; eauto.
Qed.

Definition mem_equiv m1 m2 := stack_stable m1 m2 /\ validw m1 =2 validw m2.

Lemma exec_syscallSu scs m o vargs rscs rm vres :
  exec_syscall_u scs m o vargs = ok (rscs, rm, vres) →
  mem_equiv m rm.
Proof.
  rewrite /exec_syscall_u; case: o => [ p ].
  by t_xrbindP => -[scs' v'] /= _ _ <- _.
Qed.

End SourceSysCall.

Section Section.

Context {pd: PointerData} {syscall_state : Type} {sc_sem : syscall_sem syscall_state}.

Definition exec_getrandom_s_core (scs : syscall_state_t) (m : mem) (sys_num: pointer) (p:pointer) (len:pointer) (_flag:pointer) : exec (syscall_state_t * mem * pointer) := 
  Let _ := assert (Z.eqb (wunsigned sys_num) (syscall_num (RandomBytes 1))) ErrType in 
  let len := wunsigned len in
  let sd := syscall.get_random scs len in
  Let m := fill_mem m p sd.2 in
  ok (sd.1, m, p).

Lemma exec_getrandom_s_core_stable scs m sys_num p len _fl rscs rm rp : 
  exec_getrandom_s_core scs m sys_num p len _fl = ok (rscs, rm, rp) →
  stack_stable m rm.
Proof. by rewrite /exec_getrandom_s_core; t_xrbindP => _ rm' /fill_mem_stack_stable hf ? <- ?. Qed.

Lemma exec_getrandom_s_core_validw scs m sys_num p len _fl rscs rm rp : 
  exec_getrandom_s_core scs m sys_num p len _fl = ok (rscs, rm, rp) →
  validw m =2 validw rm.
Proof. by rewrite /exec_getrandom_s_core; t_xrbindP => _ rm' /fill_mem_validw_eq hf ? <- ?. Qed.

Definition sem_syscall (o:syscall_t) : 
     syscall_state_t -> mem -> sem_prod (syscall_sig_s o).(scs_tin) (exec (syscall_state_t * mem * sem_tuple (syscall_sig_s o).(scs_tout))) := 
  match o with
  | RandomBytes _ => exec_getrandom_s_core
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
Proof.
  case: o => _len /= sys_num p len _fl [[scs' rm] t] /= hex; split.
  + by apply: exec_getrandom_s_core_stable hex. 
  by apply: exec_getrandom_s_core_validw hex.
Qed.

Lemma exec_syscallSs scs m o vargs rscs rm vres :
  exec_syscall_s scs m o vargs = ok (rscs, rm, vres) → 
  mem_equiv m rm.
Proof.
  rewrite /exec_syscall_s; t_xrbindP => -[[scs' m'] t] happ [_ <- _].
  apply (mk_forallP (sem_syscall_equiv o scs m) happ).
Qed.

End Section.

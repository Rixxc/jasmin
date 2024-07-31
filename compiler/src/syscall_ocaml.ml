type state = unit

(* FIXME syscall : I don't think that this implementation is a good one.
   But it allows to have something quick for the evaluator, so
   it is not crutial
*)

let _ =
  Random.self_init ()

let initial_state () = ()

let random_char _ =
  let n = Random.int 256 in
  Word0.wrepr Wsize.U8 (CoreConv.cz_of_int n)

let get_random (s : state) (z:BinNums.coq_Z) flag =
  let n = CoreConv.int_of_cz z in
  assert (0 <= n); s, (List.init n random_char, Word0.wrepr Wsize.U64 z)

let futex (s : state) _uaddr _futex_op _val _timeout _uaddr2 _val3 =
    s, Word0.wrepr Wsize.U64 (CoreConv.cz_of_int 0)

let mmap (s : state) _addr _len _prot _flags _filedes _off =
    s, Word0.wrepr Wsize.U64 (CoreConv.cz_of_int 0)

let sc_sem : state Syscall.syscall_sem = {
  get_random = get_random;
  futex =  futex;
  mmap = mmap;
}

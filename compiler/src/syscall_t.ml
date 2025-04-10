type 'a syscall_t =
  | RandomBytes of 'a
  | Futex
  | Mmap
  | Munmap
  | Mremap

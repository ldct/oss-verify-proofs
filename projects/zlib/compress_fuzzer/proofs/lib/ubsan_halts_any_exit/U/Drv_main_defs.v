(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.ubsan_halts_any_exit.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec Require Import Prelim STree Malloc Monad Stdio ZApi ZHarness ZInst ZTarget Target Driver Prog.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import InitMem.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.ubsan_halts_any_exit.U Require Import Layout Exit Startup Printf_stdio_iface Zlib_iface Driver_iface Drv_kit.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.World Require Import Tgt_compress_fuzzer_ubsan.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Notation usegs := Image.usegs.
Notation mem := (word -> option byte).
Notation wz := MallocRep.wz.
Notation pph := Tgt_compress_fuzzer_ubsan.M.phdrs.

From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Ceiling.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Rnd.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Local Ltac OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib.ZBridge.flia ::= first [ assumption | OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib.ZBridge.slim; lia | lia ].
Local Ltac OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib.ZBridge.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Definition RMAIN_RET : Z := 0x23130.
Definition RP1 : Z := 0x15bc8.
Definition RUSAGE : Z := 0x15d30.
Definition RSTDERR_GOT : Z := 0x2c520.

End WithCeiling0.
Notation RSTAGE := 0x2d7d9%Z (only parsing).

Section WithCeiling1. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Section CTX.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid : word) (TID : Z).
  Notation usp0 := (bv_unsigned sp0).

  (* the stack floor BASE carries on from at_main, whose stack conjunct at is
     `stk .. (usp0 - 6144513) (usp0 + -48)` (the ruled figure); ceil_ok stays at 8388608 (the heap ceiling) *)
  Definition LO : Z := usp0 - 6144513.

  Definition MFRAME (mm : mem) (pad : list byte) (s7v s6v s5v s4v : word) : Prop :=
    rw_cells usegs mm (usp0 + -128)
      [CB 8 pad; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 (wz (envp_addr sp0 argv)); C8 (wz RMAIN);
       C8 (wz (argc argv)); C8 (wz (usp0 + 8)); C8 (wz RMAIN_RET)].

  Definition ESTAT (mm : mem) : Prop :=
    rw_cells usegs mm 0x3d828 [C8 (wz 0x3d828); C8 (wz 0x3d828); C8 (wz 0x3d828); C8 (wz 0); C4 (wz TID)]
    /\ rw_cells usegs mm 0x5db58 [C4 (wz 0)]
    /\ rw_cells usegs mm 0x2c570 [C8 (wz 0x2c380); C8 (wz 0x2c378)]
    /\ rw_cells usegs mm 0x2c378 [C8 (wz 0x15b08)]
    /\ rw_cells usegs mm 0x2d7d8 [C1 (Z_to_bv 8 0)]
    /\ rw_cells usegs mm 0x2c510 [C8 (wz 0x2358c); C8 (wz 0)]
    /\ rw_cells usegs mm 0x2d580 [C8 (wz 0x2d580)]
    /\ rw_cells usegs mm 0x5dfb0 [C8 (wz 0)]
    /\ rw_cells usegs mm 0x5dfa0 [C8 (wz 0)]
    /\ rw_cells usegs mm 0x2d780 [C8 (wz RSTDOUT)]
    /\ rw_cells usegs mm 0x2d690 [C8 (wz RSTDERR)]
    /\ rw_cells usegs mm RGOT_LLVMINIT [C8 (wz 0)].

  Definition estat_addr (a : Z) : Prop :=
    (0x3d828 <= a < 0x3d84c) \/ (0x5db58 <= a < 0x5db58 + 4) \/ (0x2c570 <= a < 0x2c570 + 16) \/ (0x2c378 <= a < 0x2c380)
    \/ (0x2d7d8 <= a < 0x2d7d9) \/ (0x2c510 <= a < 0x2c520) \/ (0x5dfb0 <= a < 0x5dfb8) \/ (0x5dfa0 <= a < 0x5dfa8)
    \/ (0x2d780 <= a < 0x2d788) \/ (0x2d690 <= a < 0x2d698) \/ (0x2c528 <= a < 0x2c528 + 8) \/ (0x2d580 <= a < 0x2d580 + 8).

  Definition BASE (mm : mem) : Prop :=
    stk usegs mm LO (usp0 + -128) /\ mem_inv usegs mm /\ ESTAT mm /\ rauxv_ok mm usp0
    /\ ssp_cells mm rr_guard /\ lx_statics mm
    (* the entry block is the family's img_at ('s build_stack_bytes), the
       conjunct at_main states *)
    /\ bytes_at usegs mm usp0 (img_at sp0 argv envp uid).

  Definition P1 (ms : machine_state) : Prop :=
    exists (t0 t1 t2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (mm : mem) (pad : list byte),
      ms = MS (mkR (wz RMAIN_RET) (wz (usp0 + -128)) (wz 0x10800) (wz RATP) t0 t1 t2
                   (wz 2) (wz 2) (wz 2) (wz (usp0 + 8)) (wz (envp_addr sp0 argv)) a3 a4 a5 a6 a7
                   (wz RMAIN) (wz (envp_addr sp0 argv)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              bvmap_empty (wz RP1) (Z_to_bv 32 0) None mm (seg_rom usegs)
      /\ MFRAME mm pad s7 s6 s5 s4 /\ BASE mm
      /\ RHEAP (ps_init (reservedZ usegs)) [] mm
      /\ rw_cells usegs mm (errno_addr (wz RATP)) [C4 (wz 0)]
      /\ stdout_file mm stdout_init /\ stderr_wfile0 mm
      /\ zl_statics mm
      /\ rdrv_statics mm
      /\ stk usegs mm RSTAGE (RSTAGE + 65536).
End CTX.

Definition main_to_P1_stmt : Prop :=
  forall (sp0 : word) (argv envp : list (list byte)) (uid : word) (ms : machine_state),
    valid_sp sp0 -> ceil_ok sp0 -> valid_argv argv -> valid_envp envp -> entry_stack_fits sp0 argv envp ->
    launch_ok run_la sp0 (ed_top run_draw) argv envp run_execfn ->
    Z.of_nat (length argv) = 2 ->
    at_main sp0 argv envp uid ms ->
    exists TID, 0 < TID < 4194304 /\ evt usegs (P1 sp0 argv envp uid TID) ms.

Definition main_usage_stmt : Prop :=
  forall (sp0 : word) (argv envp : list (list byte)) (uid : word) (ms : machine_state),
    valid_sp sp0 -> ceil_ok sp0 -> valid_argv argv -> valid_envp envp -> entry_stack_fits sp0 argv envp ->
    launch_ok run_la sp0 (ed_top run_draw) argv envp run_execfn ->
    Z.of_nat (length argv) <> 2 ->
    at_main sp0 argv envp uid ms ->
    implM usegs (io_diag io (DUsage (nth 0 (argv_Z argv) [])) ;;; mret 2) (ps_init (reservedZ usegs))
          (fun code s' ms' => at_exit ps_so code s' ms') ms.
End WithCeiling1.

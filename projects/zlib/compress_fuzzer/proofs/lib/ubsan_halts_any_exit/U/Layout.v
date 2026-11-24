(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Notation usegs := Image.usegs.

Notation RGP := 0x10800%Z (only parsing).
Notation RLIBC := 0x5db80%Z (only parsing).
Notation RTLL := 0x5d8f8%Z (only parsing).
Notation RTD := 0x3d828%Z (only parsing).
Notation RTP := 0x3d8f0%Z (only parsing).
Notation RSYSINFO := 0x5db68%Z (only parsing).
Notation RDEFSTACK := 0x2d788%Z (only parsing).
Notation RGOT_DYNAMIC := 0x2c4e8%Z (only parsing).
Notation RGOT_SSP := 0x2c568%Z (only parsing).
Notation RGUARD := 0x5db60%Z (only parsing).
Notation RENVIRON := 0x3d820%Z (only parsing).
Notation RPROGNAME := 0x5db70%Z (only parsing).
Notation RHWCAP := 0x5dbe8%Z (only parsing).
Notation RGOT3 := 0x2c540%Z (only parsing).

Definition file_cells (flags : word) (wend wpos wbase writefn buf bufsize fd : Z) (mode : word) (lbf : Z) (tail : list byte) : list cell :=
  [C4 flags; C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0x25d3c);
   C8 (Z_to_bv 64 wend); C8 (Z_to_bv 64 wpos); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 wbase); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 writefn); C8 (Z_to_bv 64 0x25ef8); C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 bufsize);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 fd); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 mode; C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 lbf); C4 (Z_to_bv 64 0);
   CB 80 tail].

Notation RSTDOUT := 0x2d698%Z (only parsing).
Notation RSTDOUT_BUF := 0x5dfc8%Z (only parsing).
Notation RSTDERR := 0x2d5a8%Z (only parsing).
Notation F_STDOUT_WRITE := 0x25f00%Z (only parsing).
Notation F_STDIO_WRITE := 0x25d68%Z (only parsing).

Definition GLOBALS_TOP : Z := 0x5f000.
Definition STATIC_SPLIT : Z := 0x2c000.

Definition got_ssp := 0x2c568%Z.
Definition ssp_guard := 0x5db60%Z.
Definition ssp_cells (m : word -> option byte) (canary : word) : Prop :=
  rw_cells usegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells usegs m ssp_guard [C8 canary].

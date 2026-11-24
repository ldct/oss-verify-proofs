(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import InitMem Z_kit.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.ubsan_halts_any_exit.U Require Import Zlib_iface Z_dview Z_drep Z_dkit Z_trees_iface Z_adler32 F_memset Z_dinit_kit Z_ukit Z_dreset.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface DeflateState Trees DeflateLz Deflate RefDeflateInitLib FillWinModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Notation wz := (Z_to_bv 64).
Ltac rpc := apply ret_pc_even; [lia| reflexivity].
(* deflateResetKeep for every level: example_large's UBSan walk (Zl_dreset9), generalized over the level
   branch the way the plain port generalizes it. *)
Lemma state_check_cases : forall d, deflateStateCheck d = false ->
  let st := ds_status d in st = 42 \/ st = 57 \/ st = 69 \/ st = 73 \/ st = 91 \/ st = 103 \/ st = 113 \/ st = 666.
Proof.
  intros d H. unfold deflateStateCheck in H. apply negb_false_iff in H. cbv zeta.
  unfold INIT_STATE, GZIP_STATE, EXTRA_STATE, NAME_STATE, COMMENT_STATE, HCRC_STATE, BUSY_STATE, FINISH_STATE in H.
  repeat (apply orb_true_iff in H; destruct H as [H|H]); apply Z.eqb_eq in H; lia.
Qed.
Ltac merge44 H k :=
  lazymatch type of H with rw_cells ?segs ?m ?A ?cs =>
    let pre := eval cbv beta iota delta [firstn] in (firstn k cs) in
    let rest := eval cbv beta iota delta [skipn] in (skipn k cs) in
    lazymatch rest with C4 ?a :: C4 ?b :: ?post =>
      let H' := fresh in pose proof (cells_merge44 m A pre a b post H) as H'; cbn [app] in H'; clear H; rename H' into H end end.
Ltac split8 H k :=
  lazymatch type of H with rw_cells ?segs ?m ?A ?cs =>
    let pre := eval cbv beta iota delta [firstn] in (firstn k cs) in
    let rest := eval cbv beta iota delta [skipn] in (skipn k cs) in
    lazymatch rest with C8 (Z_to_bv 64 0) :: ?post =>
      let H' := fresh in pose proof (cells_split8_0 m A pre post H) as H'; cbn [app] in H'; clear H; rename H' into H end end.
Ltac al8m X := rewrite (land7_of_mod8 X) by (Z.div_mod_to_equations; lia).

Section RESET.
  Hypothesis HTRI : tr_init_stmt.

  Lemma deflateResetKeep_spec : forall (L : dlay) (s : deflate_state)
         (ni ai ti no ao to : Z) (p1 p2 : list byte) (msg opq dt : word) (p3 : list byte) (adl resv : word) (lo : Z)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem),
    DSTi m L s ->
    rw_cells usegs m (dl_S L) (zs_raw (dl_As L) ni ai ti no ao to p1 p2 msg opq dt p3 adl resv) ->
    deflateStateCheck s = false -> 0 <= ds_wrap s <= 1 ->
    ds_matches s = 0 -> ds_gzhead s = 0 ->
    stk usegs m lo (bv_unsigned sp) -> dlay_below L lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 160 ->
    mem_inv usegs m ->
    a0 = wz (dl_S L) ->
    evt usegs (dresetkeep_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L s ni ai no ao p1 p2 opq p3 resv lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz Z_DRESETKEEP) fc None m (seg_rom usegs)).
  Proof.
    intros until m. intros ST ZS CHK WR HM0 HGZ STK BEL LOSP MI ->.
    open_DST ST. open_A GA. unfold zs_raw, zs_pub in ZS. cbn [app] in ZS.
    lay_open LAY. below_open BEL.
    pose proof (lo_S _ LAY) as (_ & ALS & _). pose proof (lo_s _ LAY) as (_ & ALs & _).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    assert (EUS : bv_unsigned (wz (dl_S L)) = dl_S L) by (apply unsigned_lit; lia).
    assert (EUs : bv_unsigned (wz (dl_As L)) = dl_As L) by (apply unsigned_lit; lia).
    assert (EUb : bv_unsigned (wz (dl_Ab L)) = dl_Ab L) by (apply unsigned_lit; lia).
    assert (E32 : bv_unsigned (wz (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
    pose proof (munch_refl [(lo, bv_unsigned sp); (dl_S L, dl_S L + 112); (dl_As L, dl_As L + 5968)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    pose proof (munch_refl [(lo, bv_unsigned sp); (dl_S L, dl_S L + 112); (dl_As L, dl_As L + 212)] m) as MUf.
    unfold Z_DRESETKEEP.
    carve_frame 32%nat STK.
    zstep. zstep. zstep. zstep. zstep.
    zstep. zstep. if_false. zstep. al8m (dl_S L). zstep. if_false.
    zstep. zstep. if_false. zstep. zstep. if_false.
    zstep. zstep. if_false. zstep. al8m (dl_As L). zstep. if_false.
    zstep. zstep. if_false.
    zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply (evt_cut usegs (fun ms' => exists a3' a4' : word,
        ms' = MS (mkR ra (wz (bv_unsigned sp + -32)) gp tp t0 t1 t2 (wz (dl_As L)) s1 (wz (dl_S L)) (wz (-2)) (sx32 (wz (ds_status s)))
                      a3' a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x16f6c) fc None mm (seg_rom usegs))) end.
    { pose proof (state_check_cases s CHK) as CS. cbv zeta in CS.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        let bs := eval vm_compute in (option.default [] (image_bytes usegs 0x106e0 8)) in
        assert (MASK : ro_cells usegs mm 0x106e0 [CB (length bs) bs])
          by (apply ro_cells_image; [assumption| vm_compute; reflexivity| lia| cbn; lia]) end.
      cbn [length] in MASK.
      destruct CS as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; rewrite E.
      - zstep. zstep. if_true. zstep. zstep. if_false. zstep. zstep. if_true. apply evt_done. do 2 eexists. reflexivity.
      - zstep. zstep. if_false. do 4 zstep. zstep. if_false. apply evt_done. do 2 eexists. reflexivity.
      - zstep. zstep. if_false. do 4 zstep. zstep. if_false. apply evt_done. do 2 eexists. reflexivity.
      - zstep. zstep. if_false. do 4 zstep. zstep. if_false. apply evt_done. do 2 eexists. reflexivity.
      - zstep. zstep. if_false. do 4 zstep. zstep. if_false. apply evt_done. do 2 eexists. reflexivity.
      - zstep. zstep. if_false. do 4 zstep. zstep. if_false. apply evt_done. do 2 eexists. reflexivity.
      - zstep. zstep. if_false. do 4 zstep. zstep. if_false. apply evt_done. do 2 eexists. reflexivity.
      - zstep. zstep. if_true. zstep. zstep. if_true. apply evt_done. do 2 eexists. reflexivity. }
    intros ms' (a3' & a4' & ->).
    zs. zs. zs. zs. zs. zs. zs. zs. zs.
    zstep. if_cases K; zify_cond K; rewrite ?signed_wz in K by lia; [|exfalso; lia]. clear K.
    zs.
    zstep. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia; [exfalso; lia|]. clear K.
    zs. zs. zs. zs.
    zstep. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia; [exfalso; lia|]. clear K.
    zs. zs. zstep.
    remember (wz (bv_unsigned sp + -32)) as spw eqn:Espw.
    lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut; [eapply (adler32_null_spec lo) with (adler := 0) (len := 0); [lia| lia| lia| eassumption| rewrite E32; exact STK| rewrite E32; unfold ADLER32_FRAME; lia] | post_call segs mm] end.
    lazymatch goal with H : stk usegs _ lo (bv_unsigned spw) |- _ => rewrite E32 in H; rename H into STK' end.
    subst spw.
    zs. zs. zs. zs. zs. zs. zs.
    (* every level (compress2's deflateInit takes 0..9). level <> 0: bnez taken, s2 stays 0;
       level = 0: lui; add; lw s2 = matches, which is 0 here (HM0). Both paths meet after mv a0,s0. *)
    eapply (evt_cut usegs (fun ms' => ms' = _)).
    { zstep. if_cases K.
      - zs. apply evt_done. reflexivity.
      - tr_groups MUf WM. open_D GD. rewrite HM0 in GD.
        zs. zs. zs. zs. apply evt_done. reflexivity. }
    intros ms' ->.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (ST1 : DSTi mm L (RK0 s)) end.
    { tr_groups MUf WM.
      constructor; [ | exact GB | exact GC | exact GD | exact Glt | exact Gdt | exact Gbt | exact Gblc | exact Gheap | exact Gdep
                   | exact Gwin | exact Gprev | exact Ghead | exact Gpend | close_lens LENS | exact LAY ].
      do 5 eexists. unfold dsA_cells, RK0. dsred.
        replace (ds_wrap s =? 2) with false by (symmetry; apply Z.eqb_neq; lia). unfold INIT_STATE.
        rewrite HGZ.
        close_cells GA. }
    clear GA GB GC GD Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead Gpend MUf.
    zstep.
    call (HTRI L (RK0 s)).
    1:{ exact ST1. } 1:{ eassumption. } 1:{ reflexivity. }
    clear ST1.
    remember (tr_init (RK0 s)) as Y eqn:EY.
    open_DST POST. open_A GA. open_D GD.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (munch_refl [(dl_As L, dl_As L + 212); (dl_As L + 5881, dl_As L + 5968)] mm) as MUk;
      pose proof (wmono_refl usegs mm) as WMk end.
    zs. zs. zs. zs. zs. zs. zs. zs. zs. zs. zs.
    zs. zs. zs. zs. zs. zs. zs.
    release_frame FR STK' (bv_unsigned sp).
    apply evt_done. unfold dresetkeep_post. do 15 eexists. eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
    split; [lazymatch goal with H : mem_inv usegs ?mm |- mem_inv usegs ?mm => exact H end|].
    split; [exact STK'|]. split; [reflexivity|].
    split; [unfold zs_raw, zs_pub; cbn [app]; exact ZS|].
    tr_groups MUk WMk.
    unfold RK1. rewrite <- EY.
    constructor.
    -
      abstract (do 5 eexists; unfold dsA_cells, rk1_fields; dsred; close_cells GA;
        unfold zx32; f_equal; rewrite unsigned_lit_wrap; apply Z.mod_mod_divide; exists 4294967296; reflexivity).
    - abstract (exact GB).
    - abstract (exact GC).
    -
      abstract (do 5 eexists; unfold dsD_cells, rk1_fields; dsred; close_cells GD; rewrite EY, tr_init_matches; reflexivity).
    - abstract (exact Glt).
    - abstract (exact Gdt).
    - abstract (exact Gbt).
    - abstract (exact Gblc).
    - abstract (exact Gheap).
    - abstract (exact Gdep).
    - abstract (exact Gwin).
    - abstract (exact Gprev).
    - abstract (exact Ghead).
    - abstract (exact Gpend).
    - lazymatch goal with H : dlens Y |- _ => abstract (close_lens H) end.
    - exact LAY.
  Qed.
End RESET.

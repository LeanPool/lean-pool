/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk014Compact001Block008

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk014Compact001Part041`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_hwnisodm (A : Class) :
    Nominal.NPrf (.classEq (syn_cdm (syn_chwniso A)) (syn_chwcn A)) :=
  by
  let proofSupport : Finset Var := A.fv
  let u : Var := freshVar proofSupport 0
  let v : Var := freshVar proofSupport 1
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (h)
  have fresh_v : v ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_v_not_A : v ∉ A.fv := by
    intro h
    exact fresh_v (h)
  have fresh_u_ne_v : u ≠ v :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_v_ne_u : v ≠ u := Ne.symm fresh_u_ne_v
  have dv_cache_0001 : v ∉ ((Class.cv u)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_v_ne_u, not_false_eq_true])
  have dv_cache_0002 : v ∉ ((syn_chwniso A)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          fresh_v_not_A, not_false_eq_true])
  have dv_cache_0003 : u ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show u ≠ v from (by exact fresh_u_ne_v))
  have dv_cache_0004 : v ∉ ((Wff.classMem (.cv u) (syn_chwcn A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union,
          Finset.mem_singleton, fresh_v_ne_u, fresh_v_not_A, or_false, not_false_eq_true])
  have dv_cache_0005 : u ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_A, not_false_eq_true])
  have dv_cache_0006 :
    v ∉
      ((syn_wb (syn_wbr (.cv u) (syn_chwniso A) (.cv u)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A)))
            (syn_wbr (.cv u) (syn_chwiso A) (.cv u))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwiso, Finset.mem_union,
          Finset.mem_singleton, fresh_v_ne_u, fresh_v_not_A, or_false, not_false_eq_true])
  have dv_cache_0007 : u ∉ ((syn_cdm (syn_chwniso A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, fresh_u_not_A,
          not_false_eq_true])
  have dv_cache_0008 : u ∉ ((syn_chwcn A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          fresh_u_not_A, not_false_eq_true])
  have p0000 := @g_eldm v (.cv u) (syn_chwniso A) dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_biimpi (.classMem (.cv u) (syn_cdm (syn_chwniso A)))
      (syn_wex v (syn_wbr (.cv u) (syn_chwniso A) (.cv v))) p0000
  have p0002 := @g_hwnisohwisob v u A dv_cache_0003
  have p0003 :=
    @g_biimpi (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wbr (.cv u) (syn_chwiso A) (.cv v)))
      p0002
  have p0004 :=
    @g_simpld (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (syn_wbr (.cv u) (syn_chwiso A) (.cv v)) p0003
  have p0005 :=
    @g_simpl (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))
  have p0006 :=
    @g_syl (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (.classMem (.cv u) (syn_chwcn A)) p0004 p0005
  have p0007 :=
    @g_exlimiv (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (.classMem (.cv u) (syn_chwcn A))
      v dv_cache_0004 p0006
  have p0008 :=
    @g_syl (.classMem (.cv u) (syn_cdm (syn_chwniso A)))
      (syn_wex v (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))
      (.classMem (.cv u) (syn_chwcn A)) p0001 p0007
  have p0009 := @g_pm4_24 (.classMem (.cv u) (syn_chwcn A))
  have p0010 :=
    @g_biimpi (.classMem (.cv u) (syn_chwcn A))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A))) p0009
  have p0011 := @g_hwcnraw u A
  have p0012 := @g_hwisorefl u A dv_cache_0005
  have p0013 :=
    @g_syl (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcodes A))
      (syn_wbr (.cv u) (syn_chwiso A) (.cv u)) p0011 p0012
  have p0014 :=
    @g_jca (.classMem (.cv u) (syn_chwcn A))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A)))
      (syn_wbr (.cv u) (syn_chwiso A) (.cv u)) p0010 p0013
  have p0015 := @g_elex (.cv u) (syn_chwcn A)
  have p0016 := @g_breq2 (.cv v) (.cv u) (.cv u) (syn_chwniso A)
  have p0017 := @g_eleq1 (.cv v) (.cv u) (syn_chwcn A)
  have p0018 :=
    @g_anbi2d (.classEq (.cv v) (.cv u)) (.classMem (.cv v) (syn_chwcn A))
      (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A)) p0017
  have p0019 := @g_breq2 (.cv v) (.cv u) (.cv u) (syn_chwiso A)
  have p0020 :=
    @g_anbi12d (.classEq (.cv v) (.cv u))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A)))
      (syn_wbr (.cv u) (syn_chwiso A) (.cv v)) (syn_wbr (.cv u) (syn_chwiso A) (.cv u))
      p0018 p0019
  have p0021 :=
    @g_bibi12d (.classEq (.cv v) (.cv u)) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
      (syn_wbr (.cv u) (syn_chwniso A) (.cv u))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wbr (.cv u) (syn_chwiso A) (.cv v)))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A)))
        (syn_wbr (.cv u) (syn_chwiso A) (.cv u)))
      p0016 p0020
  have p0023 :=
    @g_vtoclg
      (syn_wb (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (syn_wbr (.cv u) (syn_chwiso A) (.cv v))))
      (syn_wb (syn_wbr (.cv u) (syn_chwniso A) (.cv u)) (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A)))
          (syn_wbr (.cv u) (syn_chwiso A) (.cv u))))
      v (.cv u) (syn_cvv) dv_cache_0001 dv_cache_0006 p0021 p0002
  have p0024 :=
    @g_syl (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv u) (syn_cvv))
      (syn_wb (syn_wbr (.cv u) (syn_chwniso A) (.cv u)) (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A)))
          (syn_wbr (.cv u) (syn_chwiso A) (.cv u))))
      p0015 p0023
  have p0025 :=
    @g_mpbird (.classMem (.cv u) (syn_chwcn A)) (syn_wbr (.cv u) (syn_chwniso A) (.cv u))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A)))
        (syn_wbr (.cv u) (syn_chwiso A) (.cv u)))
      p0014 p0024
  have p0026 := @g_breldm (.cv u) (.cv u) (syn_chwniso A)
  have p0027 :=
    @g_syl (.classMem (.cv u) (syn_chwcn A)) (syn_wbr (.cv u) (syn_chwniso A) (.cv u))
      (.classMem (.cv u) (syn_cdm (syn_chwniso A))) p0025 p0026
  have p0028 :=
    @g_impbii (.classMem (.cv u) (syn_cdm (syn_chwniso A)))
      (.classMem (.cv u) (syn_chwcn A)) p0008 p0027
  have p0029 :=
    @g_eqriv u (syn_cdm (syn_chwniso A)) (syn_chwcn A) dv_cache_0007 dv_cache_0008 p0028
  exact p0029

@[expose]
noncomputable def g_hwnisoclasseqb (v : Var) (u : Var) (A : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A (syn_cvv))
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wb
          (.classEq (syn_cec (.cv u) (syn_chwniso A)) (syn_cec (.cv v) (syn_chwniso A)))
          (syn_wbr (.cv u) (syn_chwniso A) (.cv v)))) :=
  by
  have p0000 :=
    @g_simpl (.classMem A (syn_cvv))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
  have p0001 := @g_hwnisoerv A
  have p0002 :=
    @g_syl
      (syn_wa (.classMem A (syn_cvv))
        (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
      (.classMem A (syn_cvv)) (syn_wbr (syn_chwniso A) (syn_cer) (syn_cvv)) p0000 p0001
  have p0003 := @g_hwnisodm A
  have p0004 :=
    @g_a1i (.classEq (syn_cdm (syn_chwniso A)) (syn_chwcn A))
      (syn_wa (.classMem A (syn_cvv))
        (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
      p0003
  have p0005 :=
    @g_simpr (.classMem A (syn_cvv))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
  have p0006 :=
    @g_simpl (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))
  have p0007 :=
    @g_syl
      (syn_wa (.classMem A (syn_cvv))
        (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (.classMem (.cv u) (syn_chwcn A)) p0005 p0006
  have p0008 := @g_elex (.cv u) (syn_chwcn A)
  have p0009 :=
    @g_syl
      (syn_wa (.classMem A (syn_cvv))
        (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
      (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv u) (syn_cvv)) p0007 p0008
  have p0011 :=
    @g_simpr (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))
  have p0012 :=
    @g_syl
      (syn_wa (.classMem A (syn_cvv))
        (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (.classMem (.cv v) (syn_chwcn A)) p0005 p0011
  have p0013 :=
    @g_erth2
      (syn_wa (.classMem A (syn_cvv))
        (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
      (.cv u) (.cv v) (syn_chwniso A) (syn_cvv) (syn_chwcn A) p0002 p0004 p0009 p0012
  have p0014 :=
    @g_bicomd
      (syn_wa (.classMem A (syn_cvv))
        (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
      (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
      (.classEq (syn_cec (.cv u) (syn_chwniso A)) (syn_cec (.cv v) (syn_chwniso A))) p0013
  exact p0014

@[expose]
noncomputable def g_hnordexg (A : Class) :
    Nominal.NPrf (.imp (.classMem A (syn_cvv)) (.classMem (syn_chnord A) (syn_cvv))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_chnord A))
  have p0001 := @g_hwnisoexg A
  have p0002 := @g_hwcnexg A
  have p0003 :=
    @g_jca (.classMem A (syn_cvv)) (.classMem (syn_chwniso A) (syn_cvv))
      (.classMem (syn_chwcn A) (syn_cvv)) p0001 p0002
  have p0004 := @g_qsexg (syn_chwcn A) (syn_chwniso A) (syn_cvv) (syn_cvv)
  have p0005 :=
    @g_syl (.classMem A (syn_cvv))
      (syn_wa (.classMem (syn_chwniso A) (syn_cvv)) (.classMem (syn_chwcn A) (syn_cvv)))
      (.classMem (syn_cqs (syn_chwcn A) (syn_chwniso A)) (syn_cvv)) p0003 p0004
  have p0006 :=
    @g_syl5eqel (.classMem A (syn_cvv)) (syn_chnord A)
      (syn_cqs (syn_chwcn A) (syn_chwniso A)) (syn_cvv) p0000 p0005
  exact p0006

@[expose]
noncomputable def g_hncardex (A : Class) :
    Nominal.NPrf (.classMem (syn_chncard A) (syn_cvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_chncard A))
  have p0001 := @g_ncex (syn_chnord A)
  have p0002 := @g_eqeltri (syn_chncard A) (syn_cnc (syn_chnord A)) (syn_cvv) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_hncardnc (A : Class) :
    Nominal.NPrf (.imp (.classMem A (syn_cvv)) (.classMem (syn_chncard A) (syn_cncs))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_chncard A))
  have p0001 := (Nominal.classEqRefl (syn_chnord A))
  have p0002 := @g_hwnisoexg A
  have p0003 := @g_hwcnexg A
  have p0004 :=
    @g_jca (.classMem A (syn_cvv)) (.classMem (syn_chwniso A) (syn_cvv))
      (.classMem (syn_chwcn A) (syn_cvv)) p0002 p0003
  have p0005 := @g_qsexg (syn_chwcn A) (syn_chwniso A) (syn_cvv) (syn_cvv)
  have p0006 :=
    @g_syl (.classMem A (syn_cvv))
      (syn_wa (.classMem (syn_chwniso A) (syn_cvv)) (.classMem (syn_chwcn A) (syn_cvv)))
      (.classMem (syn_cqs (syn_chwcn A) (syn_chwniso A)) (syn_cvv)) p0004 p0005
  have p0007 :=
    @g_syl5eqel (.classMem A (syn_cvv)) (syn_chnord A)
      (syn_cqs (syn_chwcn A) (syn_chwniso A)) (syn_cvv) p0001 p0006
  have p0008 := @g_ncelncs (syn_chnord A) (syn_cvv)
  have p0009 :=
    @g_syl (.classMem A (syn_cvv)) (.classMem (syn_chnord A) (syn_cvv))
      (.classMem (syn_cnc (syn_chnord A)) (syn_cncs)) p0007 p0008
  have p0010 :=
    @g_syl5eqel (.classMem A (syn_cvv)) (syn_chncard A) (syn_cnc (syn_chnord A))
      (syn_cncs) p0000 p0009
  exact p0010

@[expose]
noncomputable def g_hncardtc (A : Class)
    (hyp_hncardtc_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf
      (.classEq (syn_ctc (syn_chncard A)) (syn_cnc (syn_cpw1 (syn_chnord A)))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_chncard A))
  have p0001 := @g_tceq (syn_chncard A) (syn_cnc (syn_chnord A))
  have p0002 := Nominal.mp p0000 p0001
  have p0003 := @g_hnordex A hyp_hncardtc_1
  have p0004 := @g_tcnc (syn_chnord A) p0003
  have p0005 :=
    @g_eqtri (syn_ctc (syn_chncard A)) (syn_ctc (syn_cnc (syn_chnord A)))
      (syn_cnc (syn_cpw1 (syn_chnord A))) p0002 p0004
  exact p0005

@[expose]
noncomputable def g_hncardtc2 (A : Class)
    (hyp_hncardtc2_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf
      (.classEq (syn_ctc (syn_ctc (syn_chncard A)))
        (syn_cnc (syn_cpw1 (syn_cpw1 (syn_chnord A))))) :=
  by
  have p0000 := @g_hncardtc A hyp_hncardtc2_1
  have p0001 := @g_tceq (syn_ctc (syn_chncard A)) (syn_cnc (syn_cpw1 (syn_chnord A)))
  have p0002 := Nominal.mp p0000 p0001
  have p0003 := @g_hnordex A hyp_hncardtc2_1
  have p0004 := @g_pw1ex (syn_chnord A) p0003
  have p0005 := @g_tcnc (syn_cpw1 (syn_chnord A)) p0004
  have p0006 :=
    @g_eqtri (syn_ctc (syn_ctc (syn_chncard A)))
      (syn_ctc (syn_cnc (syn_cpw1 (syn_chnord A))))
      (syn_cnc (syn_cpw1 (syn_cpw1 (syn_chnord A)))) p0002 p0005
  exact p0006

@[expose]
noncomputable def g_hwcnbase (u : Var) (A : Class) (dv_A_u : u ∉ A.fv) :
    Nominal.NPrf
      (.imp (.classMem (.cv u) (syn_chwcn A)) (syn_wss (syn_cfv (syn_c2nd) (.cv u)) A)) :=
  by
  have dv_cache_0001 : Disjoint (A).fv ((syn_cfv (syn_c1st) (.cv u))).fv := by
    exact
      (show Disjoint (A).fv ((syn_cfv (syn_c1st) (.cv u))).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv];
          exact
            (show Disjoint ((A).fv) ((((Class.cv u)).fv) ∪ (((syn_c1st)).fv)) from
              (Finset.disjoint_union_right.mpr
                ⟨(show Disjoint ((A).fv) (((Class.cv u)).fv) from
                    (by
                      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                      exact
                        (show Disjoint ((A).fv) (({ u } : Finset Var)) from
                          (Finset.disjoint_singleton_right.mpr
                            (show u ∉ (A).fv from (by exact dv_A_u)))))),
                  (show Disjoint ((A).fv) (((syn_c1st)).fv) from
                    (by
                      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st];
                      exact
                        (show Disjoint ((A).fv) ((∅ : Finset Var)) from (by simp))))⟩))))
  have p0000 := @g_hwcnraw u A
  have p0001 := @g_hwcnpair u A
  have p0002 :=
    @g_eleq1d (.classMem (.cv u) (syn_chwcn A)) (.cv u)
      (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) (syn_chwcodes A)
      p0001
  have p0003 :=
    @g_mpbid (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcodes A))
      (.classMem (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))
        (syn_chwcodes A))
      p0000 p0002
  have p0004 := @g_fvex (.cv u) (syn_c1st)
  have p0005 := @g_fvex (.cv u) (syn_c2nd)
  have p0006 :=
    @g_elhwcodes A (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c1st) (.cv u)) dv_cache_0001
      p0004 p0005
  have p0007 :=
    @g_biimpi
      (.classMem (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))
        (syn_chwcodes A))
      (syn_wa (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u)))
        (syn_wss (syn_cfv (syn_c2nd) (.cv u)) A))
      p0006
  have p0008 :=
    @g_syl (.classMem (.cv u) (syn_chwcn A))
      (.classMem (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))
        (syn_chwcodes A))
      (syn_wa (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u)))
        (syn_wss (syn_cfv (syn_c2nd) (.cv u)) A))
      p0003 p0007
  have p0009 :=
    @g_simprd (.classMem (.cv u) (syn_chwcn A))
      (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u)))
      (syn_wss (syn_cfv (syn_c2nd) (.cv u)) A) p0008
  exact p0009

@[expose]
noncomputable def g_elhwbases (u : Var) (A : Class) (D : Class)
    (_dv_A_D : Disjoint A.fv D.fv) (dv_A_u : u ∉ A.fv) (dv_D_u : u ∉ D.fv) :
    Nominal.NPrf
      (syn_wb (.classMem D (syn_chwbases A))
        (syn_wrex u (syn_chwcn A) (.classEq D (syn_cfv (syn_c2nd) (.cv u))))) :=
  by
  have dv_cache_0001 : u ∉ (D).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_D_u, not_false_eq_true])
  have dv_cache_0002 : u ∉ ((syn_c2nd)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0003 : u ∉ ((syn_chwcn A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, dv_A_u,
          not_false_eq_true])
  have p0000 := (Nominal.classEqRefl (syn_chwbases A))
  have p0001 := @g_eleq2i (syn_chwbases A) (syn_cima (syn_c2nd) (syn_chwcn A)) D p0000
  have p0002 :=
    @g_elima u D (syn_c2nd) (syn_chwcn A) dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0003 := @g_n_2ndfo
  have p0004 := @g_fofn (syn_cvv) (syn_cvv) (syn_c2nd)
  have p0005 := Nominal.mp p0003 p0004
  have p0006 := @g_vex u
  have p0007 :=
    @g_pm3_2i (syn_wfn (syn_c2nd) (syn_cvv)) (.classMem (.cv u) (syn_cvv)) p0005 p0006
  have p0008 := @g_fnbrfvb (syn_cvv) (.cv u) D (syn_c2nd)
  have p0009 := Nominal.mp p0007 p0008
  have p0010 :=
    @g_bicomi (.classEq (syn_cfv (syn_c2nd) (.cv u)) D) (syn_wbr (.cv u) (syn_c2nd) D)
      p0009
  have p0011 := @g_eqcom (syn_cfv (syn_c2nd) (.cv u)) D
  have p0012 :=
    @g_bitri (syn_wbr (.cv u) (syn_c2nd) D) (.classEq (syn_cfv (syn_c2nd) (.cv u)) D)
      (.classEq D (syn_cfv (syn_c2nd) (.cv u))) p0010 p0011
  have p0013 :=
    @g_rexbii (syn_wbr (.cv u) (syn_c2nd) D) (.classEq D (syn_cfv (syn_c2nd) (.cv u))) u
      (syn_chwcn A) p0012
  have p0014 :=
    @g_bitri (.classMem D (syn_cima (syn_c2nd) (syn_chwcn A)))
      (syn_wrex u (syn_chwcn A) (syn_wbr (.cv u) (syn_c2nd) D))
      (syn_wrex u (syn_chwcn A) (.classEq D (syn_cfv (syn_c2nd) (.cv u)))) p0002 p0013
  have p0015 :=
    @g_bitri (.classMem D (syn_chwbases A))
      (.classMem D (syn_cima (syn_c2nd) (syn_chwcn A)))
      (syn_wrex u (syn_chwcn A) (.classEq D (syn_cfv (syn_c2nd) (.cv u)))) p0001 p0014
  exact p0015

@[expose]
noncomputable def g_hwcardsexg (A : Class) :
    Nominal.NPrf (.imp (.classMem A (syn_cvv)) (.classMem (syn_chwcards A) (syn_cvv))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_chwcards A))
  have p0001 := @g_enex
  have p0002 := @g_a1i (.classMem (syn_cen) (syn_cvv)) (.classMem A (syn_cvv)) p0001
  have p0003 := (Nominal.classEqRefl (syn_chwbases A))
  have p0004 := @g_n_2ndex
  have p0005 := @g_a1i (.classMem (syn_c2nd) (syn_cvv)) (.classMem A (syn_cvv)) p0004
  have p0006 := @g_hwcnexg A
  have p0007 :=
    @g_jca (.classMem A (syn_cvv)) (.classMem (syn_c2nd) (syn_cvv))
      (.classMem (syn_chwcn A) (syn_cvv)) p0005 p0006
  have p0008 := @g_imaexg (syn_c2nd) (syn_chwcn A) (syn_cvv) (syn_cvv)
  have p0009 :=
    @g_syl (.classMem A (syn_cvv))
      (syn_wa (.classMem (syn_c2nd) (syn_cvv)) (.classMem (syn_chwcn A) (syn_cvv)))
      (.classMem (syn_cima (syn_c2nd) (syn_chwcn A)) (syn_cvv)) p0007 p0008
  have p0010 :=
    @g_syl5eqel (.classMem A (syn_cvv)) (syn_chwbases A)
      (syn_cima (syn_c2nd) (syn_chwcn A)) (syn_cvv) p0003 p0009
  have p0011 :=
    @g_jca (.classMem A (syn_cvv)) (.classMem (syn_cen) (syn_cvv))
      (.classMem (syn_chwbases A) (syn_cvv)) p0002 p0010
  have p0012 := @g_qsexg (syn_chwbases A) (syn_cen) (syn_cvv) (syn_cvv)
  have p0013 :=
    @g_syl (.classMem A (syn_cvv))
      (syn_wa (.classMem (syn_cen) (syn_cvv)) (.classMem (syn_chwbases A) (syn_cvv)))
      (.classMem (syn_cqs (syn_chwbases A) (syn_cen)) (syn_cvv)) p0011 p0012
  have p0014 :=
    @g_syl5eqel (.classMem A (syn_cvv)) (syn_chwcards A)
      (syn_cqs (syn_chwbases A) (syn_cen)) (syn_cvv) p0000 p0013
  exact p0014

@[expose]
noncomputable def g_elhwcards (A : Class) (K : Class) (d : Var)
    (_dv_A_K : Disjoint A.fv K.fv) (dv_A_d : d ∉ A.fv) (dv_K_d : d ∉ K.fv)
    (hyp_elhwcards_1 : Nominal.NPrf (.classMem K (syn_cvv))) :
    Nominal.NPrf
      (syn_wb (.classMem K (syn_chwcards A))
        (syn_wrex d (syn_chwbases A) (.classEq K (syn_cnc (.cv d))))) :=
  by
  have dv_cache_0001 : d ∉ ((syn_chwbases A)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwbases, dv_A_d,
          not_false_eq_true])
  have dv_cache_0002 : d ∉ (K).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_K_d, not_false_eq_true])
  have dv_cache_0003 : d ∉ ((syn_cen)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen,
          compact_fv_not_mem_empty, not_false_eq_true])
  have p0000 := (Nominal.classEqRefl (syn_chwcards A))
  have p0001 := @g_eleq2i (syn_chwcards A) (syn_cqs (syn_chwbases A) (syn_cen)) K p0000
  have p0002 :=
    @g_elqs d (syn_chwbases A) K (syn_cen) dv_cache_0001 dv_cache_0002 dv_cache_0003
      hyp_elhwcards_1
  have p0003 := (Nominal.classEqRefl (syn_cnc (.cv d)))
  have p0004 := @g_eqeq2i (syn_cnc (.cv d)) (syn_cec (.cv d) (syn_cen)) K p0003
  have p0005 :=
    @g_bicomi (.classEq K (syn_cnc (.cv d))) (.classEq K (syn_cec (.cv d) (syn_cen)))
      p0004
  have p0006 :=
    @g_rexbii (.classEq K (syn_cec (.cv d) (syn_cen))) (.classEq K (syn_cnc (.cv d))) d
      (syn_chwbases A) p0005
  have p0007 :=
    @g_bitri (.classMem K (syn_cqs (syn_chwbases A) (syn_cen)))
      (syn_wrex d (syn_chwbases A) (.classEq K (syn_cec (.cv d) (syn_cen))))
      (syn_wrex d (syn_chwbases A) (.classEq K (syn_cnc (.cv d)))) p0002 p0006
  have p0008 :=
    @g_bitri (.classMem K (syn_chwcards A))
      (.classMem K (syn_cqs (syn_chwbases A) (syn_cen)))
      (syn_wrex d (syn_chwbases A) (.classEq K (syn_cnc (.cv d)))) p0001 p0007
  exact p0008

@[expose]
noncomputable def g_hwcardssnc (A : Class) :
    Nominal.NPrf (syn_wss (syn_chwcards A) (syn_cncs)) :=
  by
  let proofSupport : Finset Var := A.fv
  let k : Var := freshVar proofSupport 0
  let d : Var := freshVar proofSupport 1
  have fresh_k : k ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_k_not_A : k ∉ A.fv := by
    intro h
    exact fresh_k (h)
  have fresh_d : d ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_d_not_A : d ∉ A.fv := by
    intro h
    exact fresh_d (h)
  have fresh_k_ne_d : k ≠ d :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_d_ne_k : d ≠ k := Ne.symm fresh_k_ne_d
  have dv_cache_0001 : Disjoint (A).fv ((Class.cv k)).fv := by
    exact
      (show Disjoint (A).fv ((Class.cv k)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((A).fv) (({ k } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show k ∉ (A).fv from (by exact fresh_k_not_A))))))
  have dv_cache_0002 : d ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_d_not_A, not_false_eq_true])
  have dv_cache_0003 : d ∉ ((Class.cv k)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_d_ne_k, not_false_eq_true])
  have dv_cache_0004 : k ∉ ((syn_chwcards A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards,
          fresh_k_not_A, not_false_eq_true])
  have dv_cache_0005 : k ∉ ((syn_cncs)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs,
          compact_fv_not_mem_empty, not_false_eq_true])
  have p0000 := @g_vex k
  have p0001 := @g_elhwcards A (.cv k) d dv_cache_0001 dv_cache_0002 dv_cache_0003 p0000
  have p0002 :=
    @g_biimpi (.classMem (.cv k) (syn_chwcards A))
      (syn_wrex d (syn_chwbases A) (.classEq (.cv k) (syn_cnc (.cv d)))) p0001
  have p0003 := @g_rexex (.classEq (.cv k) (syn_cnc (.cv d))) d (syn_chwbases A)
  have p0004 :=
    @g_syl (.classMem (.cv k) (syn_chwcards A))
      (syn_wrex d (syn_chwbases A) (.classEq (.cv k) (syn_cnc (.cv d))))
      (syn_wex d (.classEq (.cv k) (syn_cnc (.cv d)))) p0002 p0003
  have p0005 := @g_elncs d (.cv k) dv_cache_0003
  have p0006 :=
    @g_biimpri (.classMem (.cv k) (syn_cncs))
      (syn_wex d (.classEq (.cv k) (syn_cnc (.cv d)))) p0005
  have p0007 :=
    @g_syl (.classMem (.cv k) (syn_chwcards A))
      (syn_wex d (.classEq (.cv k) (syn_cnc (.cv d)))) (.classMem (.cv k) (syn_cncs))
      p0004 p0006
  have p0008 := @g_ssriv k (syn_chwcards A) (syn_cncs) dv_cache_0004 dv_cache_0005 p0007
  exact p0008

@[expose]
noncomputable def g_frrd (ph : Wff) (x : Var) (y : Var) (z : Var) (B : Class) (S : Class)
    (dv_B_x : x ∉ B.fv) (_dv_B_y : y ∉ B.fv) (_dv_B_z : z ∉ B.fv) (dv_S_x : x ∉ S.fv)
    (dv_S_y : y ∉ S.fv) (dv_S_z : z ∉ S.fv) (dv_ph_x : x ∉ ph.fv) (dv_x_y : x ≠ y)
    (dv_x_z : x ≠ z) (dv_y_z : y ≠ z)
    (hyp_frrd_1 : Nominal.NPrf (.imp ph (.classMem S (syn_cvv))))
    (hyp_frrd_2 : Nominal.NPrf (.imp ph (.classMem B (syn_cvv))))
    (hyp_frrd_3 : Nominal.NPrf
        (.imp (syn_wa ph (syn_wa (syn_wss (.cv x) B) (syn_wne (.cv x) (syn_c0))))
          (syn_wrex z (.cv x)
            (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) S (.cv z)) (.objEq y z)))))) :
    Nominal.NPrf (.imp ph (syn_wbr S (syn_cfound) B)) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var) ∪ B.fv ∪
      S.fv
  let a : Var := freshVar proofSupport 0
  let r : Var := freshVar proofSupport 1
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_ne_x : a ≠ x := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_x_ne_a : x ≠ a := Ne.symm fresh_a_ne_x
  have fresh_a_ne_y : a ≠ y := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_a_ne_z : a ≠ z := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_a_not_B : a ∉ B.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_a_not_S : a ∉ S.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have fresh_r : r ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_r_ne_x : r ≠ x := by
    intro h
    exact
      fresh_r
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_x_ne_r : x ≠ r := Ne.symm fresh_r_ne_x
  have fresh_r_ne_y : r ≠ y := by
    intro h
    exact
      fresh_r
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_y_ne_r : y ≠ r := Ne.symm fresh_r_ne_y
  have fresh_r_ne_z : r ≠ z := by
    intro h
    exact
      fresh_r
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_z_ne_r : z ≠ r := Ne.symm fresh_r_ne_z
  have fresh_r_not_B : r ∉ B.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_r_not_S : r ∉ S.fv := by
    intro h
    exact fresh_r (Finset.mem_union_right _ (h))
  have fresh_a_ne_r : a ≠ r :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_r_ne_a : r ≠ a := Ne.symm fresh_a_ne_r
  have dv_cache_0001 : x ∉ (ph).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_ph_x, not_false_eq_true])
  have dv_cache_0002 : z ∉ ((Wff.classEq (.cv r) S)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_r, dv_S_z, or_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((Wff.classEq (.cv r) S)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_r, dv_S_y, or_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((Wff.classEq (.cv r) S)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_r, dv_S_x, or_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((Wff.classEq (.cv a) B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_a, dv_B_x, or_false, not_false_eq_true])
  have dv_cache_0006 : a ≠ r :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show a ≠ r from (by exact fresh_a_ne_r))
  have dv_cache_0007 : a ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show a ≠ x from (by exact fresh_a_ne_x))
  have dv_cache_0008 : a ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show a ≠ y from (by exact fresh_a_ne_y))
  have dv_cache_0009 : a ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show a ≠ z from (by exact fresh_a_ne_z))
  have dv_cache_0010 : r ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show r ≠ x from (by exact fresh_r_ne_x))
  have dv_cache_0011 : r ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show r ≠ y from (by exact fresh_r_ne_y))
  have dv_cache_0012 : r ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show r ≠ z from (by exact fresh_r_ne_z))
  have dv_cache_0013 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0014 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact (show x ≠ z from (by exact dv_x_z))
  have dv_cache_0015 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (show y ≠ z from (by exact dv_y_z))
  have dv_cache_0016 : r ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_r_not_S, not_false_eq_true])
  have dv_cache_0017 : a ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_S, not_false_eq_true])
  have dv_cache_0018 : r ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_r_not_B, not_false_eq_true])
  have dv_cache_0019 : a ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_B, not_false_eq_true])
  have dv_cache_0020 :
    r ∉
      ((Wff.all x (.imp (syn_wa (syn_wss (.cv x) B) (syn_wne (.cv x) (syn_c0)))
            (syn_wrex z (.cv x) (syn_wral y (.cv x)
                (.imp (syn_wbr (.cv y) S (.cv z)) (.classEq (.cv y) (.cv z)))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_all,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_r_ne_x, fresh_r_not_B, fresh_r_ne_y, fresh_r_ne_z,
          fresh_r_not_S, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0021 :
    a ∉
      ((Wff.all x (.imp (syn_wa (syn_wss (.cv x) B) (syn_wne (.cv x) (syn_c0)))
            (syn_wrex z (.cv x) (syn_wral y (.cv x)
                (.imp (syn_wbr (.cv y) S (.cv z)) (.classEq (.cv y) (.cv z)))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_all,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_a_ne_x, fresh_a_not_B, fresh_a_ne_y, fresh_a_ne_z,
          fresh_a_not_S, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0022 : r ≠ a :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (show r ≠ a from (by exact fresh_r_ne_a))
  have p0000_e00_recanon :
    Nominal.NPrf
      (.imp (syn_wa ph (syn_wa (syn_wss (.cv x) B) (syn_wne (.cv x) (syn_c0))))
        (syn_wrex z (.cv x) (syn_wral y (.cv x)
            (.imp (syn_wbr (.cv y) S (.cv z)) (.classEq (.cv y) (.cv z)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_wrex syn_wex syn_wral syn_wbr syn_cop syn_cun syn_cnin syn_wnan
          syn_ccompl
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.all
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _)
      hyp_frrd_3
  have p0000 :=
    @g_ex ph (syn_wa (syn_wss (.cv x) B) (syn_wne (.cv x) (syn_c0)))
      (syn_wrex z (.cv x) (syn_wral y (.cv x)
          (.imp (syn_wbr (.cv y) S (.cv z)) (.classEq (.cv y) (.cv z)))))
      p0000_e00_recanon
  have p0001 :=
    @g_alrimiv ph
      (.imp (syn_wa (syn_wss (.cv x) B) (syn_wne (.cv x) (syn_c0))) (syn_wrex z (.cv x)
          (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) S (.cv z)) (.classEq (.cv y) (.cv z))))))
      x dv_cache_0001 p0000
  have p0002 :=
    @g_jca ph (.classMem S (syn_cvv)) (.classMem B (syn_cvv)) hyp_frrd_1 hyp_frrd_2
  have p0003 := @g_breq (.cv y) (.cv z) (.cv r) S
  have p0004 :=
    @g_imbi1d (.classEq (.cv r) S) (syn_wbr (.cv y) (.cv r) (.cv z))
      (syn_wbr (.cv y) S (.cv z)) (.classEq (.cv y) (.cv z)) p0003
  have p0005 :=
    @g_rexralbidv (.classEq (.cv r) S)
      (.imp (syn_wbr (.cv y) (.cv r) (.cv z)) (.classEq (.cv y) (.cv z)))
      (.imp (syn_wbr (.cv y) S (.cv z)) (.classEq (.cv y) (.cv z))) z y (.cv x) (.cv x)
      dv_cache_0002 dv_cache_0003 p0004
  have p0006 :=
    @g_imbi2d (.classEq (.cv r) S)
      (syn_wrex z (.cv x) (syn_wral y (.cv x)
          (.imp (syn_wbr (.cv y) (.cv r) (.cv z)) (.classEq (.cv y) (.cv z)))))
      (syn_wrex z (.cv x) (syn_wral y (.cv x)
          (.imp (syn_wbr (.cv y) S (.cv z)) (.classEq (.cv y) (.cv z)))))
      (syn_wa (syn_wss (.cv x) (.cv a)) (syn_wne (.cv x) (syn_c0))) p0005
  have p0007 :=
    @g_albidv (.classEq (.cv r) S)
      (.imp (syn_wa (syn_wss (.cv x) (.cv a)) (syn_wne (.cv x) (syn_c0))) (syn_wrex z (.cv x)
          (syn_wral y (.cv x)
            (.imp (syn_wbr (.cv y) (.cv r) (.cv z)) (.classEq (.cv y) (.cv z))))))
      (.imp (syn_wa (syn_wss (.cv x) (.cv a)) (syn_wne (.cv x) (syn_c0))) (syn_wrex z (.cv x)
          (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) S (.cv z)) (.classEq (.cv y) (.cv z))))))
      x dv_cache_0004 p0006
  have p0008 := @g_sseq2 (.cv a) B (.cv x)
  have p0009 :=
    @g_anbi1d (.classEq (.cv a) B) (syn_wss (.cv x) (.cv a)) (syn_wss (.cv x) B)
      (syn_wne (.cv x) (syn_c0)) p0008
  have p0010 :=
    @g_imbi1d (.classEq (.cv a) B)
      (syn_wa (syn_wss (.cv x) (.cv a)) (syn_wne (.cv x) (syn_c0)))
      (syn_wa (syn_wss (.cv x) B) (syn_wne (.cv x) (syn_c0)))
      (syn_wrex z (.cv x) (syn_wral y (.cv x)
          (.imp (syn_wbr (.cv y) S (.cv z)) (.classEq (.cv y) (.cv z)))))
      p0009
  have p0011 :=
    @g_albidv (.classEq (.cv a) B)
      (.imp (syn_wa (syn_wss (.cv x) (.cv a)) (syn_wne (.cv x) (syn_c0))) (syn_wrex z (.cv x)
          (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) S (.cv z)) (.classEq (.cv y) (.cv z))))))
      (.imp (syn_wa (syn_wss (.cv x) B) (syn_wne (.cv x) (syn_c0))) (syn_wrex z (.cv x)
          (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) S (.cv z)) (.classEq (.cv y) (.cv z))))))
      x dv_cache_0005 p0010
  have p0012 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_found x y z r a
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
  have p0013_e02_recanon :
    Nominal.NPrf
      (.classEq (syn_cfound) (syn_copab r a (.all x
            (.imp (syn_wa (syn_wss (.cv x) (.cv a)) (syn_wne (.cv x) (syn_c0)))
              (syn_wrex z (.cv x) (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) (.cv r) (.cv z))
                    (.classEq (.cv y) (.cv z))))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cfound syn_copab syn_wex syn_wa syn_wss syn_cin syn_ccompl syn_cnin
          syn_wnan syn_wne syn_c0 syn_cdif syn_cvv syn_wrex syn_wral syn_wbr syn_cop
          syn_cun
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_all,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.classEq
        · exact Nominal.RecanonTransportDev.TRecanonClass.same _
        · apply Nominal.RecanonTransportDev.TRecanonClass.cab
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.all
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.all
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · apply Nominal.RecanonTransportDev.TRecanonWff.neg
                apply Nominal.RecanonTransportDev.TRecanonWff.all
                apply Nominal.RecanonTransportDev.TRecanonWff.imp
                · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                  · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                  · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _)
      p0012
  have p0013 :=
    @g_brabg
      (.all x (.imp (syn_wa (syn_wss (.cv x) (.cv a)) (syn_wne (.cv x) (syn_c0)))
          (syn_wrex z (.cv x) (syn_wral y (.cv x)
              (.imp (syn_wbr (.cv y) (.cv r) (.cv z)) (.classEq (.cv y) (.cv z)))))))
      (.all x (.imp (syn_wa (syn_wss (.cv x) (.cv a)) (syn_wne (.cv x) (syn_c0)))
          (syn_wrex z (.cv x) (syn_wral y (.cv x)
              (.imp (syn_wbr (.cv y) S (.cv z)) (.classEq (.cv y) (.cv z)))))))
      (.all x (.imp (syn_wa (syn_wss (.cv x) B) (syn_wne (.cv x) (syn_c0))) (syn_wrex z (.cv x)
            (syn_wral y (.cv x)
              (.imp (syn_wbr (.cv y) S (.cv z)) (.classEq (.cv y) (.cv z)))))))
      r a S B (syn_cvv) (syn_cvv) (syn_cfound) dv_cache_0016 dv_cache_0017 dv_cache_0018
      dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 p0007 p0011
      p0013_e02_recanon
  have p0014 :=
    @g_syl ph (syn_wa (.classMem S (syn_cvv)) (.classMem B (syn_cvv)))
      (syn_wb (syn_wbr S (syn_cfound) B) (.all x
          (.imp (syn_wa (syn_wss (.cv x) B) (syn_wne (.cv x) (syn_c0))) (syn_wrex z (.cv x)
              (syn_wral y (.cv x)
                (.imp (syn_wbr (.cv y) S (.cv z)) (.classEq (.cv y) (.cv z))))))))
      p0002 p0013
  have p0015 :=
    @g_mpbird ph (syn_wbr S (syn_cfound) B)
      (.all x (.imp (syn_wa (syn_wss (.cv x) B) (syn_wne (.cv x) (syn_c0))) (syn_wrex z (.cv x)
            (syn_wral y (.cv x)
              (.imp (syn_wbr (.cv y) S (.cv z)) (.classEq (.cv y) (.cv z)))))))
      p0001 p0014
  exact p0015


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk014Compact001Part042`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_hwnisohwisocl (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv)))
        (.imp (syn_wbr B (syn_chwniso A) C) (syn_wbr B (syn_chwiso A) C))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  let v : Var := freshVar proofSupport 0
  let u : Var := freshVar proofSupport 1
  have fresh_v : v ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_v_not_A : v ∉ A.fv := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_v_not_B : v ∉ B.fv := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_v_not_C : v ∉ C.fv := by
    intro h
    exact fresh_v (Finset.mem_union_right _ (h))
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_u_not_B : u ∉ B.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_v_ne_u : v ≠ u :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_u_ne_v : u ≠ v := Ne.symm fresh_v_ne_u
  have dv_cache_0001 : u ≠ v := by exact (show u ≠ v from (by exact fresh_u_ne_v))
  have dv_cache_0002 : u ∉ (B).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_B, not_false_eq_true])
  have dv_cache_0003 :
    u ∉
      ((Wff.imp (syn_wbr B (syn_chwniso A) (.cv v)) (syn_wbr B (syn_chwiso A) (.cv v)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwiso, Finset.mem_union,
          Finset.mem_singleton, fresh_u_not_B, fresh_u_ne_v, fresh_u_not_A, or_false,
          not_false_eq_true])
  have dv_cache_0004 : v ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_v_not_C, not_false_eq_true])
  have dv_cache_0005 :
    v ∉
      ((Wff.imp (.classMem B (syn_cvv))
          (.imp (syn_wbr B (syn_chwniso A) C) (syn_wbr B (syn_chwiso A) C)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwiso, Finset.mem_union,
          fresh_v_not_B, fresh_v_not_C, fresh_v_not_A, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have p0000 := @g_simpl (.classMem B (syn_cvv)) (.classMem C (syn_cvv))
  have p0001 := @g_simpr (.classMem B (syn_cvv)) (.classMem C (syn_cvv))
  have p0002 := @g_breq2 (.cv v) C B (syn_chwniso A)
  have p0003 := @g_breq2 (.cv v) C B (syn_chwiso A)
  have p0004 :=
    @g_imbi12d (.classEq (.cv v) C) (syn_wbr B (syn_chwniso A) (.cv v))
      (syn_wbr B (syn_chwniso A) C) (syn_wbr B (syn_chwiso A) (.cv v))
      (syn_wbr B (syn_chwiso A) C) p0002 p0003
  have p0005 :=
    @g_imbi2d (.classEq (.cv v) C)
      (.imp (syn_wbr B (syn_chwniso A) (.cv v)) (syn_wbr B (syn_chwiso A) (.cv v)))
      (.imp (syn_wbr B (syn_chwniso A) C) (syn_wbr B (syn_chwiso A) C))
      (.classMem B (syn_cvv)) p0004
  have p0006 := @g_breq1 (.cv u) B (.cv v) (syn_chwniso A)
  have p0007 := @g_breq1 (.cv u) B (.cv v) (syn_chwiso A)
  have p0008 :=
    @g_imbi12d (.classEq (.cv u) B) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
      (syn_wbr B (syn_chwniso A) (.cv v)) (syn_wbr (.cv u) (syn_chwiso A) (.cv v))
      (syn_wbr B (syn_chwiso A) (.cv v)) p0006 p0007
  have p0009 := @g_hwnisohwisob v u A dv_cache_0001
  have p0010 :=
    @g_biimpi (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wbr (.cv u) (syn_chwiso A) (.cv v)))
      p0009
  have p0011 :=
    @g_simprd (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (syn_wbr (.cv u) (syn_chwiso A) (.cv v)) p0010
  have p0012 :=
    @g_vtoclg
      (.imp (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wbr (.cv u) (syn_chwiso A) (.cv v)))
      (.imp (syn_wbr B (syn_chwniso A) (.cv v)) (syn_wbr B (syn_chwiso A) (.cv v))) u B
      (syn_cvv) dv_cache_0002 dv_cache_0003 p0008 p0011
  have p0013 :=
    @g_vtoclg
      (.imp (.classMem B (syn_cvv))
        (.imp (syn_wbr B (syn_chwniso A) (.cv v)) (syn_wbr B (syn_chwiso A) (.cv v))))
      (.imp (.classMem B (syn_cvv))
        (.imp (syn_wbr B (syn_chwniso A) C) (syn_wbr B (syn_chwiso A) C)))
      v C (syn_cvv) dv_cache_0004 dv_cache_0005 p0005 p0012
  have p0014 :=
    @g_syl (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv)))
      (.classMem C (syn_cvv))
      (.imp (.classMem B (syn_cvv))
        (.imp (syn_wbr B (syn_chwniso A) C) (syn_wbr B (syn_chwiso A) C)))
      p0001 p0013
  have p0015 :=
    @g_mpd (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv)))
      (.classMem B (syn_cvv))
      (.imp (syn_wbr B (syn_chwniso A) C) (syn_wbr B (syn_chwiso A) C)) p0000 p0014
  exact p0015

@[expose]
noncomputable def g_hwisowitnesscl (A : Class) (B : Class) (C : Class) (h : Var)
    (dv_A_h : h ∉ A.fv) (dv_B_h : h ∉ B.fv) (dv_C_h : h ∉ C.fv) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv)))
        (.imp (syn_wbr B (syn_chwiso A) C) (syn_wex h
            (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C)
              (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) C))))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ ({ h } : Finset Var)
  let v : Var := freshVar proofSupport 0
  let u : Var := freshVar proofSupport 1
  have fresh_v : v ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_v_not_A : v ∉ A.fv := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_v_not_B : v ∉ B.fv := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_v_not_C : v ∉ C.fv := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_v_ne_h : v ≠ h := by
    intro h
    exact fresh_v (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_h_ne_v : h ≠ v := Ne.symm fresh_v_ne_h
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_u_not_B : u ∉ B.fv := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_u_ne_h : u ≠ h := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_h_ne_u : h ≠ u := Ne.symm fresh_u_ne_h
  have fresh_v_ne_u : v ≠ u :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_u_ne_v : u ≠ v := Ne.symm fresh_v_ne_u
  have dv_cache_0001 : h ∉ ((Wff.classEq (.cv v) C)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_h_ne_v, dv_C_h, or_false, not_false_eq_true])
  have dv_cache_0002 : h ∉ ((Wff.classEq (.cv u) B)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_h_ne_u, dv_B_h, or_false, not_false_eq_true])
  have dv_cache_0003 : h ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_h, not_false_eq_true])
  have dv_cache_0004 : h ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show h ≠ u from (by exact fresh_h_ne_u))
  have dv_cache_0005 : h ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show h ≠ v from (by exact fresh_h_ne_v))
  have dv_cache_0006 : u ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_B, not_false_eq_true])
  have dv_cache_0007 :
    u ∉
      ((Wff.imp (syn_wbr B (syn_chwiso A) (.cv v)) (syn_wex h
            (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v))
              (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwiso,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_u_not_B, fresh_u_ne_v,
          fresh_u_not_A, fresh_u_ne_h, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0008 : v ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_v_not_C, not_false_eq_true])
  have dv_cache_0009 :
    v ∉
      ((Wff.imp (.classMem B (syn_cvv)) (.imp (syn_wbr B (syn_chwiso A) C) (syn_wex h
              (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C)
                (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) C)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwiso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_v_not_B, fresh_v_not_C,
          fresh_v_not_A, fresh_v_ne_h, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have p0000 := @g_simpl (.classMem B (syn_cvv)) (.classMem C (syn_cvv))
  have p0001 := @g_simpr (.classMem B (syn_cvv)) (.classMem C (syn_cvv))
  have p0002 := @g_breq2 (.cv v) C B (syn_chwiso A)
  have p0003 := @g_fveq2 (.cv v) C (syn_c1st)
  have p0004 :=
    @g_isoeq3 (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c1st) B)
      (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) C) (.cv h)
  have p0005 :=
    @g_syl (.classEq (.cv v) C)
      (.classEq (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) C))
      (syn_wb (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v)))
        (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C)
          (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v))))
      p0003 p0004
  have p0006 := @g_fveq2 (.cv v) C (syn_c2nd)
  have p0007 :=
    @g_isoeq5 (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) C)
      (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C) (.cv h)
  have p0008 :=
    @g_syl (.classEq (.cv v) C)
      (.classEq (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) C))
      (syn_wb (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C)
          (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v)))
        (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C)
          (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) C)))
      p0006 p0007
  have p0009 :=
    @g_bitrd (.classEq (.cv v) C)
      (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v))
        (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v)))
      (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C)
        (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v)))
      (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C)
        (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) C))
      p0005 p0008
  have p0010 :=
    @g_exbidv (.classEq (.cv v) C)
      (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v))
        (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v)))
      (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C)
        (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) C))
      h dv_cache_0001 p0009
  have p0011 :=
    @g_imbi12d (.classEq (.cv v) C) (syn_wbr B (syn_chwiso A) (.cv v))
      (syn_wbr B (syn_chwiso A) C)
      (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v))))
      (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C)
          (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) C)))
      p0002 p0010
  have p0012 :=
    @g_imbi2d (.classEq (.cv v) C)
      (.imp (syn_wbr B (syn_chwiso A) (.cv v)) (syn_wex h
          (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v)))))
      (.imp (syn_wbr B (syn_chwiso A) C) (syn_wex h
          (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C)
            (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) C))))
      (.classMem B (syn_cvv)) p0011
  have p0013 := @g_breq1 (.cv u) B (.cv v) (syn_chwiso A)
  have p0014 := @g_fveq2 (.cv u) B (syn_c1st)
  have p0015 :=
    @g_isoeq2 (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))
      (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) B)
      (.cv h)
  have p0016 :=
    @g_syl (.classEq (.cv u) B)
      (.classEq (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) B))
      (syn_wb (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
        (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
      p0014 p0015
  have p0017 := @g_fveq2 (.cv u) B (syn_c2nd)
  have p0018 :=
    @g_isoeq4 (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))
      (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v)) (.cv h)
  have p0019 :=
    @g_syl (.classEq (.cv u) B)
      (.classEq (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) B))
      (syn_wb (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
        (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v))))
      p0017 p0018
  have p0020 :=
    @g_bitrd (.classEq (.cv u) B)
      (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
        (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
      (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v))
        (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
      (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v))
        (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v)))
      p0016 p0019
  have p0021 :=
    @g_exbidv (.classEq (.cv u) B)
      (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
        (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
      (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v))
        (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v)))
      h dv_cache_0002 p0020
  have p0022 :=
    @g_imbi12d (.classEq (.cv u) B) (syn_wbr (.cv u) (syn_chwiso A) (.cv v))
      (syn_wbr B (syn_chwiso A) (.cv v))
      (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
      (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v))))
      p0013 p0021
  have p0023 := @g_brhwisoany v u A h dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0024 :=
    @g_biimpi (syn_wbr (.cv u) (syn_chwiso A) (.cv v))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A)))
        (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))))
      p0023
  have p0025 :=
    @g_simprd (syn_wbr (.cv u) (syn_chwiso A) (.cv v))
      (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A)))
      (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
      p0024
  have p0026 :=
    @g_vtoclg
      (.imp (syn_wbr (.cv u) (syn_chwiso A) (.cv v)) (syn_wex h
          (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))))
      (.imp (syn_wbr B (syn_chwiso A) (.cv v)) (syn_wex h
          (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v)))))
      u B (syn_cvv) dv_cache_0006 dv_cache_0007 p0022 p0025
  have p0027 :=
    @g_vtoclg
      (.imp (.classMem B (syn_cvv)) (.imp (syn_wbr B (syn_chwiso A) (.cv v)) (syn_wex h
            (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) (.cv v))
              (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) (.cv v))))))
      (.imp (.classMem B (syn_cvv)) (.imp (syn_wbr B (syn_chwiso A) C) (syn_wex h
            (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C)
              (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) C)))))
      v C (syn_cvv) dv_cache_0008 dv_cache_0009 p0012 p0026
  have p0028 :=
    @g_syl (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv)))
      (.classMem C (syn_cvv))
      (.imp (.classMem B (syn_cvv)) (.imp (syn_wbr B (syn_chwiso A) C) (syn_wex h
            (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C)
              (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) C)))))
      p0001 p0027
  have p0029 :=
    @g_mpd (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv)))
      (.classMem B (syn_cvv))
      (.imp (syn_wbr B (syn_chwiso A) C) (syn_wex h
          (syn_wiso (.cv h) (syn_cfv (syn_c1st) B) (syn_cfv (syn_c1st) C)
            (syn_cfv (syn_c2nd) B) (syn_cfv (syn_c2nd) C))))
      p0000 p0028
  exact p0029

@[expose]
noncomputable def g_opfvscl (B : Class) (C : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv)))
        (syn_wa (.classEq (syn_cfv (syn_c1st) (syn_cop B C)) B)
          (.classEq (syn_cfv (syn_c2nd) (syn_cop B C)) C))) :=
  by
  let proofSupport : Finset Var := B.fv ∪ C.fv
  let v : Var := freshVar proofSupport 0
  let u : Var := freshVar proofSupport 1
  have fresh_v : v ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_v_not_B : v ∉ B.fv := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (h))
  have fresh_v_not_C : v ∉ C.fv := by
    intro h
    exact fresh_v (Finset.mem_union_right _ (h))
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_u_not_B : u ∉ B.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (h))
  have fresh_v_ne_u : v ≠ u :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_u_ne_v : u ≠ v := Ne.symm fresh_v_ne_u
  have dv_cache_0001 : u ∉ (B).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_B, not_false_eq_true])
  have dv_cache_0002 :
    u ∉
      ((syn_wa (.classEq (syn_cfv (syn_c1st) (syn_cop B (.cv v))) B)
          (.classEq (syn_cfv (syn_c2nd) (syn_cop B (.cv v))) (.cv v)))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          Finset.mem_singleton, fresh_u_not_B, fresh_u_ne_v, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0003 : v ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_v_not_C, not_false_eq_true])
  have dv_cache_0004 :
    v ∉
      ((Wff.imp (.classMem B (syn_cvv)) (syn_wa (.classEq (syn_cfv (syn_c1st) (syn_cop B C)) B)
            (.classEq (syn_cfv (syn_c2nd) (syn_cop B C)) C)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          fresh_v_not_B, fresh_v_not_C, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have p0000 := @g_simpl (.classMem B (syn_cvv)) (.classMem C (syn_cvv))
  have p0001 := @g_simpr (.classMem B (syn_cvv)) (.classMem C (syn_cvv))
  have p0002 := @g_opeq2 (.cv v) C B
  have p0003 :=
    @g_fveq2d (.classEq (.cv v) C) (syn_cop B (.cv v)) (syn_cop B C) (syn_c1st) p0002
  have p0004 := @g_eqid B
  have p0005 := @g_a1i (.classEq B B) (.classEq (.cv v) C) p0004
  have p0006 :=
    @g_eqeq12d (.classEq (.cv v) C) (syn_cfv (syn_c1st) (syn_cop B (.cv v)))
      (syn_cfv (syn_c1st) (syn_cop B C)) B B p0003 p0005
  have p0008 :=
    @g_fveq2d (.classEq (.cv v) C) (syn_cop B (.cv v)) (syn_cop B C) (syn_c2nd) p0002
  have p0009 := @g_id (.classEq (.cv v) C)
  have p0010 :=
    @g_eqeq12d (.classEq (.cv v) C) (syn_cfv (syn_c2nd) (syn_cop B (.cv v)))
      (syn_cfv (syn_c2nd) (syn_cop B C)) (.cv v) C p0008 p0009
  have p0011 :=
    @g_anbi12d (.classEq (.cv v) C) (.classEq (syn_cfv (syn_c1st) (syn_cop B (.cv v))) B)
      (.classEq (syn_cfv (syn_c1st) (syn_cop B C)) B)
      (.classEq (syn_cfv (syn_c2nd) (syn_cop B (.cv v))) (.cv v))
      (.classEq (syn_cfv (syn_c2nd) (syn_cop B C)) C) p0006 p0010
  have p0012 :=
    @g_imbi2d (.classEq (.cv v) C)
      (syn_wa (.classEq (syn_cfv (syn_c1st) (syn_cop B (.cv v))) B)
        (.classEq (syn_cfv (syn_c2nd) (syn_cop B (.cv v))) (.cv v)))
      (syn_wa (.classEq (syn_cfv (syn_c1st) (syn_cop B C)) B)
        (.classEq (syn_cfv (syn_c2nd) (syn_cop B C)) C))
      (.classMem B (syn_cvv)) p0011
  have p0013 := @g_opeq1 (.cv u) B (.cv v)
  have p0014 :=
    @g_fveq2d (.classEq (.cv u) B) (syn_cop (.cv u) (.cv v)) (syn_cop B (.cv v))
      (syn_c1st) p0013
  have p0015 := @g_id (.classEq (.cv u) B)
  have p0016 :=
    @g_eqeq12d (.classEq (.cv u) B) (syn_cfv (syn_c1st) (syn_cop (.cv u) (.cv v)))
      (syn_cfv (syn_c1st) (syn_cop B (.cv v))) (.cv u) B p0014 p0015
  have p0018 :=
    @g_fveq2d (.classEq (.cv u) B) (syn_cop (.cv u) (.cv v)) (syn_cop B (.cv v))
      (syn_c2nd) p0013
  have p0019 := @g_eqid (.cv v)
  have p0020 := @g_a1i (.classEq (.cv v) (.cv v)) (.classEq (.cv u) B) p0019
  have p0021 :=
    @g_eqeq12d (.classEq (.cv u) B) (syn_cfv (syn_c2nd) (syn_cop (.cv u) (.cv v)))
      (syn_cfv (syn_c2nd) (syn_cop B (.cv v))) (.cv v) (.cv v) p0018 p0020
  have p0022 :=
    @g_anbi12d (.classEq (.cv u) B)
      (.classEq (syn_cfv (syn_c1st) (syn_cop (.cv u) (.cv v))) (.cv u))
      (.classEq (syn_cfv (syn_c1st) (syn_cop B (.cv v))) B)
      (.classEq (syn_cfv (syn_c2nd) (syn_cop (.cv u) (.cv v))) (.cv v))
      (.classEq (syn_cfv (syn_c2nd) (syn_cop B (.cv v))) (.cv v)) p0016 p0021
  have p0023 := @g_vex u
  have p0024 := @g_vex v
  have p0025 := @g_opfv1st (.cv u) (.cv v) p0023 p0024
  have p0028 := @g_opfv2nd (.cv u) (.cv v) p0023 p0024
  have p0029 :=
    @g_pm3_2i (.classEq (syn_cfv (syn_c1st) (syn_cop (.cv u) (.cv v))) (.cv u))
      (.classEq (syn_cfv (syn_c2nd) (syn_cop (.cv u) (.cv v))) (.cv v)) p0025 p0028
  have p0030 :=
    @g_vtoclg
      (syn_wa (.classEq (syn_cfv (syn_c1st) (syn_cop (.cv u) (.cv v))) (.cv u))
        (.classEq (syn_cfv (syn_c2nd) (syn_cop (.cv u) (.cv v))) (.cv v)))
      (syn_wa (.classEq (syn_cfv (syn_c1st) (syn_cop B (.cv v))) B)
        (.classEq (syn_cfv (syn_c2nd) (syn_cop B (.cv v))) (.cv v)))
      u B (syn_cvv) dv_cache_0001 dv_cache_0002 p0022 p0029
  have p0031 :=
    @g_vtoclg
      (.imp (.classMem B (syn_cvv))
        (syn_wa (.classEq (syn_cfv (syn_c1st) (syn_cop B (.cv v))) B)
          (.classEq (syn_cfv (syn_c2nd) (syn_cop B (.cv v))) (.cv v))))
      (.imp (.classMem B (syn_cvv)) (syn_wa (.classEq (syn_cfv (syn_c1st) (syn_cop B C)) B)
          (.classEq (syn_cfv (syn_c2nd) (syn_cop B C)) C)))
      v C (syn_cvv) dv_cache_0003 dv_cache_0004 p0012 p0030
  have p0032 :=
    @g_syl (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv)))
      (.classMem C (syn_cvv))
      (.imp (.classMem B (syn_cvv)) (syn_wa (.classEq (syn_cfv (syn_c1st) (syn_cop B C)) B)
          (.classEq (syn_cfv (syn_c2nd) (syn_cop B C)) C)))
      p0001 p0031
  have p0033 :=
    @g_mpd (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv)))
      (.classMem B (syn_cvv))
      (syn_wa (.classEq (syn_cfv (syn_c1st) (syn_cop B C)) B)
        (.classEq (syn_cfv (syn_c2nd) (syn_cop B C)) C))
      p0000 p0032
  exact p0033


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk014Compact001Part043`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_werestr (ph : Wff) (A : Class) (B : Class) (R : Class)
    (_dv_A_R : Disjoint A.fv R.fv)
    (hyp_werestr_1 : Nominal.NPrf (.imp ph (syn_wbr R (syn_cwe) A)))
    (hyp_werestr_2 : Nominal.NPrf (.imp ph (syn_wss B A)))
    (hyp_werestr_3 : Nominal.NPrf (.imp ph (.classMem B (syn_cvv)))) :
    Nominal.NPrf (.imp ph (syn_wbr (syn_cin R (syn_cxp B B)) (syn_cwe) B)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ A.fv ∪ B.fv ∪ R.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_ph : x ∉ ph.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_ph : y ∉ ph.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_ph : z ∉ ph.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_R : z ∉ R.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_z_ne_x : z ≠ x := Ne.symm fresh_x_ne_z
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y := Ne.symm fresh_y_ne_z
  have dv_cache_0001 : x ∉ (B).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_B, not_false_eq_true])
  have dv_cache_0002 : y ∉ (B).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_B, not_false_eq_true])
  have dv_cache_0003 : z ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_B, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((syn_cin R (syn_cxp B B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union,
          fresh_x_not_R, fresh_x_not_B, or_false, not_false_eq_true])
  have dv_cache_0005 : y ∉ ((syn_cin R (syn_cxp B B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union,
          fresh_y_not_R, fresh_y_not_B, or_false, not_false_eq_true])
  have dv_cache_0006 : z ∉ ((syn_cin R (syn_cxp B B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union,
          fresh_z_not_R, fresh_z_not_B, or_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ (ph).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_ph, not_false_eq_true])
  have dv_cache_0008 : y ∉ (ph).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_ph, not_false_eq_true])
  have dv_cache_0009 : z ∉ (ph).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_ph, not_false_eq_true])
  have dv_cache_0010 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0011 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0012 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0013 : z ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_R, not_false_eq_true])
  have dv_cache_0014 : y ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_R, not_false_eq_true])
  have dv_cache_0015 : z ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_x, not_false_eq_true])
  have dv_cache_0016 : y ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_x, not_false_eq_true])
  have dv_cache_0017 : z ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (show z ≠ y from (by exact fresh_z_ne_y))
  have dv_cache_0018 :
    y ∉ ((syn_wa ph (syn_wa (syn_wss (.cv x) B) (syn_wne (.cv x) (syn_c0))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          Finset.mem_singleton, fresh_y_not_ph, fresh_y_ne_x, fresh_y_not_B,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0019 :
    z ∉ ((syn_wa ph (syn_wa (syn_wss (.cv x) B) (syn_wne (.cv x) (syn_c0))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          Finset.mem_singleton, fresh_z_not_ph, fresh_z_ne_x, fresh_z_not_B,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 := @g_brex R A (syn_cwe)
  have p0001 :=
    @g_simpld (syn_wbr R (syn_cwe) A) (.classMem R (syn_cvv)) (.classMem A (syn_cvv))
      p0000
  have p0002 :=
    @g_syl ph (syn_wbr R (syn_cwe) A) (.classMem R (syn_cvv)) hyp_werestr_1 p0001
  have p0003 :=
    @g_jca ph (.classMem B (syn_cvv)) (.classMem B (syn_cvv)) hyp_werestr_3 hyp_werestr_3
  have p0004 := @g_xpexg B B (syn_cvv) (syn_cvv)
  have p0005 :=
    @g_syl ph (syn_wa (.classMem B (syn_cvv)) (.classMem B (syn_cvv)))
      (.classMem (syn_cxp B B) (syn_cvv)) p0003 p0004
  have p0006 :=
    @g_jca ph (.classMem R (syn_cvv)) (.classMem (syn_cxp B B) (syn_cvv)) p0002 p0005
  have p0007 := @g_inexg R (syn_cxp B B) (syn_cvv) (syn_cvv)
  have p0008 :=
    @g_syl ph (syn_wa (.classMem R (syn_cvv)) (.classMem (syn_cxp B B) (syn_cvv)))
      (.classMem (syn_cin R (syn_cxp B B)) (syn_cvv)) p0006 p0007
  have p0009 := @g_simpl ph (.classMem (.cv x) B)
  have p0010 := (Nominal.classEqRefl (syn_cwe))
  have p0011 := @g_breqi R A (syn_cwe) (syn_cin (syn_cstrict) (syn_cfound)) p0010
  have p0012 := @g_brin R A (syn_cstrict) (syn_cfound)
  have p0013 :=
    @g_bitri (syn_wbr R (syn_cwe) A) (syn_wbr R (syn_cin (syn_cstrict) (syn_cfound)) A)
      (syn_wa (syn_wbr R (syn_cstrict) A) (syn_wbr R (syn_cfound) A)) p0011 p0012
  have p0014 :=
    @g_biimpi (syn_wbr R (syn_cwe) A)
      (syn_wa (syn_wbr R (syn_cstrict) A) (syn_wbr R (syn_cfound) A)) p0013
  have p0015 :=
    @g_syl ph (syn_wbr R (syn_cwe) A)
      (syn_wa (syn_wbr R (syn_cstrict) A) (syn_wbr R (syn_cfound) A)) hyp_werestr_1 p0014
  have p0016 := @g_simpld ph (syn_wbr R (syn_cstrict) A) (syn_wbr R (syn_cfound) A) p0015
  have p0017 := @g_sopc A R
  have p0018 :=
    @g_sylib ph (syn_wbr R (syn_cstrict) A)
      (syn_wa (syn_wbr R (syn_cpartial) A) (syn_wbr R (syn_cconnex) A)) p0016 p0017
  have p0019 :=
    @g_simpld ph (syn_wbr R (syn_cpartial) A) (syn_wbr R (syn_cconnex) A) p0018
  have p0020 := @g_porta A R
  have p0021 :=
    @g_sylib ph (syn_wbr R (syn_cpartial) A)
      (syn_w3a (syn_wbr R (syn_cref) A) (syn_wbr R (syn_ctrans) A) (syn_wbr R (syn_cantisym) A))
      p0019 p0020
  have p0022 :=
    @g_simp1d ph (syn_wbr R (syn_cref) A) (syn_wbr R (syn_ctrans) A)
      (syn_wbr R (syn_cantisym) A) p0021
  have p0023 :=
    @g_syl (syn_wa ph (.classMem (.cv x) B)) ph (syn_wbr R (syn_cref) A) p0009 p0022
  have p0024 := @g_sselda ph B A (.cv x) hyp_werestr_2
  have p0025 := @g_refd (syn_wa ph (.classMem (.cv x) B)) A R (.cv x) p0023 p0024
  have p0026 := @g_simpr ph (.classMem (.cv x) B)
  have p0028 :=
    @g_jca (syn_wa ph (.classMem (.cv x) B)) (.classMem (.cv x) B) (.classMem (.cv x) B)
      p0026 p0026
  have p0029 := @g_brinxp (.cv x) (.cv x) B B R
  have p0030 :=
    @g_syl (syn_wa ph (.classMem (.cv x) B))
      (syn_wa (.classMem (.cv x) B) (.classMem (.cv x) B))
      (syn_wb (syn_wbr (.cv x) R (.cv x)) (syn_wbr (.cv x) (syn_cin R (syn_cxp B B)) (.cv x)))
      p0028 p0029
  have p0031 :=
    @g_mpbid (syn_wa ph (.classMem (.cv x) B)) (syn_wbr (.cv x) R (.cv x))
      (syn_wbr (.cv x) (syn_cin R (syn_cxp B B)) (.cv x)) p0025 p0030
  have p0032 :=
    @g_simp1 ph
      (syn_w3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B))
      (syn_wa (syn_wbr (.cv x) (syn_cin R (syn_cxp B B)) (.cv y))
        (syn_wbr (.cv y) (syn_cin R (syn_cxp B B)) (.cv z)))
  have p0045 :=
    @g_simp2d ph (syn_wbr R (syn_cref) A) (syn_wbr R (syn_ctrans) A)
      (syn_wbr R (syn_cantisym) A) p0021
  have p0046 :=
    @g_syl
      (syn_w3a ph (syn_w3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B))
        (syn_wa (syn_wbr (.cv x) (syn_cin R (syn_cxp B B)) (.cv y))
          (syn_wbr (.cv y) (syn_cin R (syn_cxp B B)) (.cv z))))
      ph (syn_wbr R (syn_ctrans) A) p0032 p0045
  have p0048 :=
    @g_syl
      (syn_w3a ph (syn_w3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B))
        (syn_wa (syn_wbr (.cv x) (syn_cin R (syn_cxp B B)) (.cv y))
          (syn_wbr (.cv y) (syn_cin R (syn_cxp B B)) (.cv z))))
      ph (syn_wss B A) p0032 hyp_werestr_2
  have p0049 :=
    @g_simp2 ph
      (syn_w3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B))
      (syn_wa (syn_wbr (.cv x) (syn_cin R (syn_cxp B B)) (.cv y))
        (syn_wbr (.cv y) (syn_cin R (syn_cxp B B)) (.cv z)))
  have p0050 := @g_simp1 (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B)
  have p0051 :=
    @g_syl
      (syn_w3a ph (syn_w3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B))
        (syn_wa (syn_wbr (.cv x) (syn_cin R (syn_cxp B B)) (.cv y))
          (syn_wbr (.cv y) (syn_cin R (syn_cxp B B)) (.cv z))))
      (syn_w3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B))
      (.classMem (.cv x) B) p0049 p0050
  have p0052 :=
    @g_sseldd
      (syn_w3a ph (syn_w3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B))
        (syn_wa (syn_wbr (.cv x) (syn_cin R (syn_cxp B B)) (.cv y))
          (syn_wbr (.cv y) (syn_cin R (syn_cxp B B)) (.cv z))))
      B A (.cv x) p0048 p0051
  have p0056 := @g_simp2 (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B)
  have p0057 :=
    @g_syl
      (syn_w3a ph (syn_w3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B))
        (syn_wa (syn_wbr (.cv x) (syn_cin R (syn_cxp B B)) (.cv y))
          (syn_wbr (.cv y) (syn_cin R (syn_cxp B B)) (.cv z))))
      (syn_w3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B))
      (.classMem (.cv y) B) p0049 p0056
  have p0058 :=
    @g_sseldd
      (syn_w3a ph (syn_w3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B))
        (syn_wa (syn_wbr (.cv x) (syn_cin R (syn_cxp B B)) (.cv y))
          (syn_wbr (.cv y) (syn_cin R (syn_cxp B B)) (.cv z))))
      B A (.cv y) p0048 p0057
  have p0062 := @g_simp3 (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B)
  have p0063 :=
    @g_syl
      (syn_w3a ph (syn_w3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B))
        (syn_wa (syn_wbr (.cv x) (syn_cin R (syn_cxp B B)) (.cv y))
          (syn_wbr (.cv y) (syn_cin R (syn_cxp B B)) (.cv z))))
      (syn_w3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B))
      (.classMem (.cv z) B) p0049 p0062
  have p0064 :=
    @g_sseldd
      (syn_w3a ph (syn_w3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B))
        (syn_wa (syn_wbr (.cv x) (syn_cin R (syn_cxp B B)) (.cv y))
          (syn_wbr (.cv y) (syn_cin R (syn_cxp B B)) (.cv z))))
      B A (.cv z) p0048 p0063
  have p0065 :=
    @g_simp3 ph
      (syn_w3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B))
      (syn_wa (syn_wbr (.cv x) (syn_cin R (syn_cxp B B)) (.cv y))
        (syn_wbr (.cv y) (syn_cin R (syn_cxp B B)) (.cv z)))
  have p0066 :=
    @g_simpld
      (syn_w3a ph (syn_w3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B))
        (syn_wa (syn_wbr (.cv x) (syn_cin R (syn_cxp B B)) (.cv y))
          (syn_wbr (.cv y) (syn_cin R (syn_cxp B B)) (.cv z))))
      (syn_wbr (.cv x) (syn_cin R (syn_cxp B B)) (.cv y))
      (syn_wbr (.cv y) (syn_cin R (syn_cxp B B)) (.cv z)) p0065
  have p0067 := @g_brin (.cv x) (.cv y) R (syn_cxp B B)
  have p0068 :=
    @g_simplbi (syn_wbr (.cv x) (syn_cin R (syn_cxp B B)) (.cv y))
      (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv x) (syn_cxp B B) (.cv y)) p0067
  have p0069 :=
    @g_syl
      (syn_w3a ph (syn_w3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B))
        (syn_wa (syn_wbr (.cv x) (syn_cin R (syn_cxp B B)) (.cv y))
          (syn_wbr (.cv y) (syn_cin R (syn_cxp B B)) (.cv z))))
      (syn_wbr (.cv x) (syn_cin R (syn_cxp B B)) (.cv y)) (syn_wbr (.cv x) R (.cv y))
      p0066 p0068
  have p0071 :=
    @g_simprd
      (syn_w3a ph (syn_w3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B))
        (syn_wa (syn_wbr (.cv x) (syn_cin R (syn_cxp B B)) (.cv y))
          (syn_wbr (.cv y) (syn_cin R (syn_cxp B B)) (.cv z))))
      (syn_wbr (.cv x) (syn_cin R (syn_cxp B B)) (.cv y))
      (syn_wbr (.cv y) (syn_cin R (syn_cxp B B)) (.cv z)) p0065
  have p0072 := @g_brin (.cv y) (.cv z) R (syn_cxp B B)
  have p0073 :=
    @g_simplbi (syn_wbr (.cv y) (syn_cin R (syn_cxp B B)) (.cv z))
      (syn_wbr (.cv y) R (.cv z)) (syn_wbr (.cv y) (syn_cxp B B) (.cv z)) p0072
  have p0074 :=
    @g_syl
      (syn_w3a ph (syn_w3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B))
        (syn_wa (syn_wbr (.cv x) (syn_cin R (syn_cxp B B)) (.cv y))
          (syn_wbr (.cv y) (syn_cin R (syn_cxp B B)) (.cv z))))
      (syn_wbr (.cv y) (syn_cin R (syn_cxp B B)) (.cv z)) (syn_wbr (.cv y) R (.cv z))
      p0071 p0073
  have p0075 :=
    @g_trd
      (syn_w3a ph (syn_w3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B))
        (syn_wa (syn_wbr (.cv x) (syn_cin R (syn_cxp B B)) (.cv y))
          (syn_wbr (.cv y) (syn_cin R (syn_cxp B B)) (.cv z))))
      A R (.cv x) (.cv y) (.cv z) p0046 p0052 p0058 p0064 p0069 p0074
  have p0082 :=
    @g_jca
      (syn_w3a ph (syn_w3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B))
        (syn_wa (syn_wbr (.cv x) (syn_cin R (syn_cxp B B)) (.cv y))
          (syn_wbr (.cv y) (syn_cin R (syn_cxp B B)) (.cv z))))
      (.classMem (.cv x) B) (.classMem (.cv z) B) p0051 p0063
  have p0083 := @g_brinxp (.cv x) (.cv z) B B R
  have p0084 :=
    @g_syl
      (syn_w3a ph (syn_w3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B))
        (syn_wa (syn_wbr (.cv x) (syn_cin R (syn_cxp B B)) (.cv y))
          (syn_wbr (.cv y) (syn_cin R (syn_cxp B B)) (.cv z))))
      (syn_wa (.classMem (.cv x) B) (.classMem (.cv z) B))
      (syn_wb (syn_wbr (.cv x) R (.cv z)) (syn_wbr (.cv x) (syn_cin R (syn_cxp B B)) (.cv z)))
      p0082 p0083
  have p0085 :=
    @g_mpbid
      (syn_w3a ph (syn_w3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B))
        (syn_wa (syn_wbr (.cv x) (syn_cin R (syn_cxp B B)) (.cv y))
          (syn_wbr (.cv y) (syn_cin R (syn_cxp B B)) (.cv z))))
      (syn_wbr (.cv x) R (.cv z)) (syn_wbr (.cv x) (syn_cin R (syn_cxp B B)) (.cv z))
      p0075 p0084
  have p0086 :=
    @g_simp1 ph (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B))
      (syn_wa (syn_wbr (.cv x) (syn_cin R (syn_cxp B B)) (.cv y))
        (syn_wbr (.cv y) (syn_cin R (syn_cxp B B)) (.cv x)))
  have p0099 :=
    @g_simp3d ph (syn_wbr R (syn_cref) A) (syn_wbr R (syn_ctrans) A)
      (syn_wbr R (syn_cantisym) A) p0021
  have p0100 :=
    @g_syl
      (syn_w3a ph (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B))
        (syn_wa (syn_wbr (.cv x) (syn_cin R (syn_cxp B B)) (.cv y))
          (syn_wbr (.cv y) (syn_cin R (syn_cxp B B)) (.cv x))))
      ph (syn_wbr R (syn_cantisym) A) p0086 p0099
  have p0102 :=
    @g_syl
      (syn_w3a ph (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B))
        (syn_wa (syn_wbr (.cv x) (syn_cin R (syn_cxp B B)) (.cv y))
          (syn_wbr (.cv y) (syn_cin R (syn_cxp B B)) (.cv x))))
      ph (syn_wss B A) p0086 hyp_werestr_2
  have p0103 :=
    @g_simp2 ph (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B))
      (syn_wa (syn_wbr (.cv x) (syn_cin R (syn_cxp B B)) (.cv y))
        (syn_wbr (.cv y) (syn_cin R (syn_cxp B B)) (.cv x)))
  have p0104 :=
    @g_simpld
      (syn_w3a ph (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B))
        (syn_wa (syn_wbr (.cv x) (syn_cin R (syn_cxp B B)) (.cv y))
          (syn_wbr (.cv y) (syn_cin R (syn_cxp B B)) (.cv x))))
      (.classMem (.cv x) B) (.classMem (.cv y) B) p0103
  have p0105 :=
    @g_sseldd
      (syn_w3a ph (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B))
        (syn_wa (syn_wbr (.cv x) (syn_cin R (syn_cxp B B)) (.cv y))
          (syn_wbr (.cv y) (syn_cin R (syn_cxp B B)) (.cv x))))
      B A (.cv x) p0102 p0104
  have p0109 :=
    @g_simprd
      (syn_w3a ph (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B))
        (syn_wa (syn_wbr (.cv x) (syn_cin R (syn_cxp B B)) (.cv y))
          (syn_wbr (.cv y) (syn_cin R (syn_cxp B B)) (.cv x))))
      (.classMem (.cv x) B) (.classMem (.cv y) B) p0103
  have p0110 :=
    @g_sseldd
      (syn_w3a ph (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B))
        (syn_wa (syn_wbr (.cv x) (syn_cin R (syn_cxp B B)) (.cv y))
          (syn_wbr (.cv y) (syn_cin R (syn_cxp B B)) (.cv x))))
      B A (.cv y) p0102 p0109
  have p0111 :=
    @g_simp3 ph (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B))
      (syn_wa (syn_wbr (.cv x) (syn_cin R (syn_cxp B B)) (.cv y))
        (syn_wbr (.cv y) (syn_cin R (syn_cxp B B)) (.cv x)))
  have p0112 :=
    @g_simpld
      (syn_w3a ph (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B))
        (syn_wa (syn_wbr (.cv x) (syn_cin R (syn_cxp B B)) (.cv y))
          (syn_wbr (.cv y) (syn_cin R (syn_cxp B B)) (.cv x))))
      (syn_wbr (.cv x) (syn_cin R (syn_cxp B B)) (.cv y))
      (syn_wbr (.cv y) (syn_cin R (syn_cxp B B)) (.cv x)) p0111
  have p0115 :=
    @g_syl
      (syn_w3a ph (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B))
        (syn_wa (syn_wbr (.cv x) (syn_cin R (syn_cxp B B)) (.cv y))
          (syn_wbr (.cv y) (syn_cin R (syn_cxp B B)) (.cv x))))
      (syn_wbr (.cv x) (syn_cin R (syn_cxp B B)) (.cv y)) (syn_wbr (.cv x) R (.cv y))
      p0112 p0068
  have p0117 :=
    @g_simprd
      (syn_w3a ph (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B))
        (syn_wa (syn_wbr (.cv x) (syn_cin R (syn_cxp B B)) (.cv y))
          (syn_wbr (.cv y) (syn_cin R (syn_cxp B B)) (.cv x))))
      (syn_wbr (.cv x) (syn_cin R (syn_cxp B B)) (.cv y))
      (syn_wbr (.cv y) (syn_cin R (syn_cxp B B)) (.cv x)) p0111
  have p0118 := @g_brin (.cv y) (.cv x) R (syn_cxp B B)
  have p0119 :=
    @g_simplbi (syn_wbr (.cv y) (syn_cin R (syn_cxp B B)) (.cv x))
      (syn_wbr (.cv y) R (.cv x)) (syn_wbr (.cv y) (syn_cxp B B) (.cv x)) p0118
  have p0120 :=
    @g_syl
      (syn_w3a ph (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B))
        (syn_wa (syn_wbr (.cv x) (syn_cin R (syn_cxp B B)) (.cv y))
          (syn_wbr (.cv y) (syn_cin R (syn_cxp B B)) (.cv x))))
      (syn_wbr (.cv y) (syn_cin R (syn_cxp B B)) (.cv x)) (syn_wbr (.cv y) R (.cv x))
      p0117 p0119
  have p0121 :=
    @g_antid
      (syn_w3a ph (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B))
        (syn_wa (syn_wbr (.cv x) (syn_cin R (syn_cxp B B)) (.cv y))
          (syn_wbr (.cv y) (syn_cin R (syn_cxp B B)) (.cv x))))
      A R (.cv x) (.cv y) p0100 p0105 p0110 p0115 p0120
  have p0122 := @g_simp1 ph (.classMem (.cv x) B) (.classMem (.cv y) B)
  have p0132 :=
    @g_simprd ph (syn_wbr R (syn_cpartial) A) (syn_wbr R (syn_cconnex) A) p0018
  have p0133 :=
    @g_syl (syn_w3a ph (.classMem (.cv x) B) (.classMem (.cv y) B)) ph
      (syn_wbr R (syn_cconnex) A) p0122 p0132
  have p0135 :=
    @g_syl (syn_w3a ph (.classMem (.cv x) B) (.classMem (.cv y) B)) ph (syn_wss B A) p0122
      hyp_werestr_2
  have p0136 := @g_simp2 ph (.classMem (.cv x) B) (.classMem (.cv y) B)
  have p0137 :=
    @g_sseldd (syn_w3a ph (.classMem (.cv x) B) (.classMem (.cv y) B)) B A (.cv x) p0135
      p0136
  have p0140 := @g_simp3 ph (.classMem (.cv x) B) (.classMem (.cv y) B)
  have p0141 :=
    @g_sseldd (syn_w3a ph (.classMem (.cv x) B) (.classMem (.cv y) B)) B A (.cv y) p0135
      p0140
  have p0142 :=
    @g_connexd (syn_w3a ph (.classMem (.cv x) B) (.classMem (.cv y) B)) A R (.cv x)
      (.cv y) p0133 p0137 p0141
  have p0145 :=
    @g_jca (syn_w3a ph (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classMem (.cv x) B)
      (.classMem (.cv y) B) p0136 p0140
  have p0146 := @g_brinxp (.cv x) (.cv y) B B R
  have p0147 :=
    @g_syl (syn_w3a ph (.classMem (.cv x) B) (.classMem (.cv y) B))
      (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B))
      (syn_wb (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv x) (syn_cin R (syn_cxp B B)) (.cv y)))
      p0145 p0146
  have p0150 :=
    @g_jca (syn_w3a ph (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classMem (.cv y) B)
      (.classMem (.cv x) B) p0140 p0136
  have p0151 := @g_brinxp (.cv y) (.cv x) B B R
  have p0152 :=
    @g_syl (syn_w3a ph (.classMem (.cv x) B) (.classMem (.cv y) B))
      (syn_wa (.classMem (.cv y) B) (.classMem (.cv x) B))
      (syn_wb (syn_wbr (.cv y) R (.cv x)) (syn_wbr (.cv y) (syn_cin R (syn_cxp B B)) (.cv x)))
      p0150 p0151
  have p0153 :=
    @g_orbi12d (syn_w3a ph (.classMem (.cv x) B) (.classMem (.cv y) B))
      (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv x) (syn_cin R (syn_cxp B B)) (.cv y))
      (syn_wbr (.cv y) R (.cv x)) (syn_wbr (.cv y) (syn_cin R (syn_cxp B B)) (.cv x))
      p0147 p0152
  have p0154 :=
    @g_mpbid (syn_w3a ph (.classMem (.cv x) B) (.classMem (.cv y) B))
      (syn_wo (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv x)))
      (syn_wo (syn_wbr (.cv x) (syn_cin R (syn_cxp B B)) (.cv y))
        (syn_wbr (.cv y) (syn_cin R (syn_cxp B B)) (.cv x)))
      p0142 p0153
  have p0155_e04_recanon :
    Nominal.NPrf
      (.imp (syn_w3a ph (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B))
          (syn_wa (syn_wbr (.cv x) (syn_cin R (syn_cxp B B)) (.cv y))
            (syn_wbr (.cv y) (syn_cin R (syn_cxp B B)) (.cv x)))) (.objEq x y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_w3a syn_wa
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0121
  have p0155 :=
    @g_sod ph x y z B (syn_cin R (syn_cxp B B)) (syn_cvv) (syn_cvv) dv_cache_0001
      dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
      dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 p0008
      hyp_werestr_3 p0031 p0085 p0155_e04_recanon p0154
  have p0165 := @g_simpl ph (syn_wa (syn_wss (.cv x) B) (syn_wne (.cv x) (syn_c0)))
  have p0166 := (Nominal.classEqRefl (syn_cwe))
  have p0167 := @g_breqi R A (syn_cwe) (syn_cin (syn_cstrict) (syn_cfound)) p0166
  have p0168 := @g_brin R A (syn_cstrict) (syn_cfound)
  have p0169 :=
    @g_bitri (syn_wbr R (syn_cwe) A) (syn_wbr R (syn_cin (syn_cstrict) (syn_cfound)) A)
      (syn_wa (syn_wbr R (syn_cstrict) A) (syn_wbr R (syn_cfound) A)) p0167 p0168
  have p0170 :=
    @g_biimpi (syn_wbr R (syn_cwe) A)
      (syn_wa (syn_wbr R (syn_cstrict) A) (syn_wbr R (syn_cfound) A)) p0169
  have p0171 :=
    @g_syl ph (syn_wbr R (syn_cwe) A)
      (syn_wa (syn_wbr R (syn_cstrict) A) (syn_wbr R (syn_cfound) A)) hyp_werestr_1 p0170
  have p0172 := @g_simprd ph (syn_wbr R (syn_cstrict) A) (syn_wbr R (syn_cfound) A) p0171
  have p0173 :=
    @g_syl (syn_wa ph (syn_wa (syn_wss (.cv x) B) (syn_wne (.cv x) (syn_c0)))) ph
      (syn_wbr R (syn_cfound) A) p0165 p0172
  have p0174 := @g_vex x
  have p0175 :=
    @g_a1i (.classMem (.cv x) (syn_cvv))
      (syn_wa ph (syn_wa (syn_wss (.cv x) B) (syn_wne (.cv x) (syn_c0)))) p0174
  have p0176 := @g_simpr ph (syn_wa (syn_wss (.cv x) B) (syn_wne (.cv x) (syn_c0)))
  have p0177 :=
    @g_simpld (syn_wa ph (syn_wa (syn_wss (.cv x) B) (syn_wne (.cv x) (syn_c0))))
      (syn_wss (.cv x) B) (syn_wne (.cv x) (syn_c0)) p0176
  have p0178 := @g_simpl ph (syn_wa (syn_wss (.cv x) B) (syn_wne (.cv x) (syn_c0)))
  have p0179 :=
    @g_syl (syn_wa ph (syn_wa (syn_wss (.cv x) B) (syn_wne (.cv x) (syn_c0)))) ph
      (syn_wss B A) p0178 hyp_werestr_2
  have p0180 :=
    @g_sstrd (syn_wa ph (syn_wa (syn_wss (.cv x) B) (syn_wne (.cv x) (syn_c0)))) (.cv x) B
      A p0177 p0179
  have p0181 := @g_simpr ph (syn_wa (syn_wss (.cv x) B) (syn_wne (.cv x) (syn_c0)))
  have p0182 :=
    @g_simprd (syn_wa ph (syn_wa (syn_wss (.cv x) B) (syn_wne (.cv x) (syn_c0))))
      (syn_wss (.cv x) B) (syn_wne (.cv x) (syn_c0)) p0181
  have p0183 :=
    @g_frd (syn_wa ph (syn_wa (syn_wss (.cv x) B) (syn_wne (.cv x) (syn_c0)))) z y A R
      (syn_cvv) (.cv x) dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
      dv_cache_0017 p0173 p0175 p0180 p0182
  have p0184 := @g_brin (.cv y) (.cv z) R (syn_cxp B B)
  have p0185 :=
    @g_simplbi (syn_wbr (.cv y) (syn_cin R (syn_cxp B B)) (.cv z))
      (syn_wbr (.cv y) R (.cv z)) (syn_wbr (.cv y) (syn_cxp B B) (.cv z)) p0184
  have p0186 :=
    @g_imim1i (syn_wbr (.cv y) (syn_cin R (syn_cxp B B)) (.cv z))
      (syn_wbr (.cv y) R (.cv z)) (.classEq (.cv y) (.cv z)) p0185
  have p0187 :=
    @g_a1i
      (.imp (.imp (syn_wbr (.cv y) R (.cv z)) (.classEq (.cv y) (.cv z)))
        (.imp (syn_wbr (.cv y) (syn_cin R (syn_cxp B B)) (.cv z)) (.classEq (.cv y) (.cv z))))
      (syn_wa ph (syn_wa (syn_wss (.cv x) B) (syn_wne (.cv x) (syn_c0)))) p0186
  have p0188 :=
    @g_ralimdv (syn_wa ph (syn_wa (syn_wss (.cv x) B) (syn_wne (.cv x) (syn_c0))))
      (.imp (syn_wbr (.cv y) R (.cv z)) (.classEq (.cv y) (.cv z)))
      (.imp (syn_wbr (.cv y) (syn_cin R (syn_cxp B B)) (.cv z)) (.classEq (.cv y) (.cv z)))
      y (.cv x) dv_cache_0018 p0187
  have p0189 :=
    @g_reximdv (syn_wa ph (syn_wa (syn_wss (.cv x) B) (syn_wne (.cv x) (syn_c0))))
      (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) R (.cv z)) (.classEq (.cv y) (.cv z))))
      (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) (syn_cin R (syn_cxp B B)) (.cv z))
          (.classEq (.cv y) (.cv z))))
      z (.cv x) dv_cache_0019 p0188
  have p0190_e00_recanon :
    Nominal.NPrf
      (.imp (syn_wa ph (syn_wa (syn_wss (.cv x) B) (syn_wne (.cv x) (syn_c0))))
        (syn_wrex z (.cv x) (syn_wral y (.cv x)
            (.imp (syn_wbr (.cv y) R (.cv z)) (.classEq (.cv y) (.cv z)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_wrex syn_wex syn_wral syn_wbr syn_cop syn_cun syn_cnin syn_wnan
          syn_ccompl
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.all
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _)
      p0183
  have p0190 :=
    @g_mpd (syn_wa ph (syn_wa (syn_wss (.cv x) B) (syn_wne (.cv x) (syn_c0))))
      (syn_wrex z (.cv x) (syn_wral y (.cv x)
          (.imp (syn_wbr (.cv y) R (.cv z)) (.classEq (.cv y) (.cv z)))))
      (syn_wrex z (.cv x) (syn_wral y (.cv x)
          (.imp (syn_wbr (.cv y) (syn_cin R (syn_cxp B B)) (.cv z))
            (.classEq (.cv y) (.cv z)))))
      p0190_e00_recanon p0189
  have p0191_e02_recanon :
    Nominal.NPrf
      (.imp (syn_wa ph (syn_wa (syn_wss (.cv x) B) (syn_wne (.cv x) (syn_c0))))
        (syn_wrex z (.cv x) (syn_wral y (.cv x)
            (.imp (syn_wbr (.cv y) (syn_cin R (syn_cxp B B)) (.cv z)) (.objEq y z))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_wrex syn_wex syn_wral syn_wbr syn_cop syn_cun syn_cnin syn_wnan
          syn_ccompl syn_cin syn_cxp syn_copab
        simp (config :=
          {
            failIfUnchanged :=
              false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.all
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0190
  have p0191 :=
    @g_frrd ph x y z B (syn_cin R (syn_cxp B B)) dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0010 dv_cache_0011
      dv_cache_0012 p0008 hyp_werestr_3 p0191_e02_recanon
  have p0192 :=
    @g_jca ph (syn_wbr (syn_cin R (syn_cxp B B)) (syn_cstrict) B)
      (syn_wbr (syn_cin R (syn_cxp B B)) (syn_cfound) B) p0155 p0191
  have p0194 :=
    @g_breqi (syn_cin R (syn_cxp B B)) B (syn_cwe) (syn_cin (syn_cstrict) (syn_cfound))
      p0010
  have p0195 := @g_brin (syn_cin R (syn_cxp B B)) B (syn_cstrict) (syn_cfound)
  have p0196 :=
    @g_bitri (syn_wbr (syn_cin R (syn_cxp B B)) (syn_cwe) B)
      (syn_wbr (syn_cin R (syn_cxp B B)) (syn_cin (syn_cstrict) (syn_cfound)) B)
      (syn_wa (syn_wbr (syn_cin R (syn_cxp B B)) (syn_cstrict) B)
        (syn_wbr (syn_cin R (syn_cxp B B)) (syn_cfound) B))
      p0194 p0195
  have p0197 :=
    @g_a1i
      (syn_wb (syn_wbr (syn_cin R (syn_cxp B B)) (syn_cwe) B)
        (syn_wa (syn_wbr (syn_cin R (syn_cxp B B)) (syn_cstrict) B)
          (syn_wbr (syn_cin R (syn_cxp B B)) (syn_cfound) B)))
      ph p0196
  have p0198 :=
    @g_mpbird ph (syn_wbr (syn_cin R (syn_cxp B B)) (syn_cwe) B)
      (syn_wa (syn_wbr (syn_cin R (syn_cxp B B)) (syn_cstrict) B)
        (syn_wbr (syn_cin R (syn_cxp B B)) (syn_cfound) B))
      p0192 p0197
  exact p0198


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk014Compact001Part044`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_werestrndv (ph : Wff) (B : Class) (D : Class) (S : Class)
    (hyp_werestrndv_1 : Nominal.NPrf (.imp ph (syn_wbr S (syn_cwe) D)))
    (hyp_werestrndv_2 : Nominal.NPrf (.imp ph (syn_wss B D)))
    (hyp_werestrndv_3 : Nominal.NPrf (.imp ph (.classMem B (syn_cvv)))) :
    Nominal.NPrf (.imp ph (syn_wbr (syn_cin S (syn_cxp B B)) (syn_cwe) B)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ B.fv ∪ D.fv ∪ S.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_ph : x ∉ ph.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_S : x ∉ S.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_ph : y ∉ ph.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_S : y ∉ S.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_ph : z ∉ ph.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_not_S : z ∉ S.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_z_ne_x : z ≠ x := Ne.symm fresh_x_ne_z
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y := Ne.symm fresh_y_ne_z
  have dv_cache_0001 : x ∉ (B).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_B, not_false_eq_true])
  have dv_cache_0002 : y ∉ (B).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_B, not_false_eq_true])
  have dv_cache_0003 : z ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_B, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((syn_cin S (syn_cxp B B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union,
          fresh_x_not_S, fresh_x_not_B, or_false, not_false_eq_true])
  have dv_cache_0005 : y ∉ ((syn_cin S (syn_cxp B B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union,
          fresh_y_not_S, fresh_y_not_B, or_false, not_false_eq_true])
  have dv_cache_0006 : z ∉ ((syn_cin S (syn_cxp B B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union,
          fresh_z_not_S, fresh_z_not_B, or_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ (ph).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_ph, not_false_eq_true])
  have dv_cache_0008 : y ∉ (ph).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_ph, not_false_eq_true])
  have dv_cache_0009 : z ∉ (ph).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_ph, not_false_eq_true])
  have dv_cache_0010 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0011 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0012 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0013 : z ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_S, not_false_eq_true])
  have dv_cache_0014 : y ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_S, not_false_eq_true])
  have dv_cache_0015 : z ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_x, not_false_eq_true])
  have dv_cache_0016 : y ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_x, not_false_eq_true])
  have dv_cache_0017 : z ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (show z ≠ y from (by exact fresh_z_ne_y))
  have dv_cache_0018 :
    y ∉ ((syn_wa ph (syn_wa (syn_wss (.cv x) B) (syn_wne (.cv x) (syn_c0))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          Finset.mem_singleton, fresh_y_not_ph, fresh_y_ne_x, fresh_y_not_B,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0019 :
    z ∉ ((syn_wa ph (syn_wa (syn_wss (.cv x) B) (syn_wne (.cv x) (syn_c0))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          Finset.mem_singleton, fresh_z_not_ph, fresh_z_ne_x, fresh_z_not_B,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 := @g_brex S D (syn_cwe)
  have p0001 :=
    @g_simpld (syn_wbr S (syn_cwe) D) (.classMem S (syn_cvv)) (.classMem D (syn_cvv))
      p0000
  have p0002 :=
    @g_syl ph (syn_wbr S (syn_cwe) D) (.classMem S (syn_cvv)) hyp_werestrndv_1 p0001
  have p0003 :=
    @g_jca ph (.classMem B (syn_cvv)) (.classMem B (syn_cvv)) hyp_werestrndv_3
      hyp_werestrndv_3
  have p0004 := @g_xpexg B B (syn_cvv) (syn_cvv)
  have p0005 :=
    @g_syl ph (syn_wa (.classMem B (syn_cvv)) (.classMem B (syn_cvv)))
      (.classMem (syn_cxp B B) (syn_cvv)) p0003 p0004
  have p0006 :=
    @g_jca ph (.classMem S (syn_cvv)) (.classMem (syn_cxp B B) (syn_cvv)) p0002 p0005
  have p0007 := @g_inexg S (syn_cxp B B) (syn_cvv) (syn_cvv)
  have p0008 :=
    @g_syl ph (syn_wa (.classMem S (syn_cvv)) (.classMem (syn_cxp B B) (syn_cvv)))
      (.classMem (syn_cin S (syn_cxp B B)) (syn_cvv)) p0006 p0007
  have p0009 := @g_simpl ph (.classMem (.cv x) B)
  have p0010 := (Nominal.classEqRefl (syn_cwe))
  have p0011 := @g_breqi S D (syn_cwe) (syn_cin (syn_cstrict) (syn_cfound)) p0010
  have p0012 := @g_brin S D (syn_cstrict) (syn_cfound)
  have p0013 :=
    @g_bitri (syn_wbr S (syn_cwe) D) (syn_wbr S (syn_cin (syn_cstrict) (syn_cfound)) D)
      (syn_wa (syn_wbr S (syn_cstrict) D) (syn_wbr S (syn_cfound) D)) p0011 p0012
  have p0014 :=
    @g_biimpi (syn_wbr S (syn_cwe) D)
      (syn_wa (syn_wbr S (syn_cstrict) D) (syn_wbr S (syn_cfound) D)) p0013
  have p0015 :=
    @g_syl ph (syn_wbr S (syn_cwe) D)
      (syn_wa (syn_wbr S (syn_cstrict) D) (syn_wbr S (syn_cfound) D)) hyp_werestrndv_1
      p0014
  have p0016 := @g_simpld ph (syn_wbr S (syn_cstrict) D) (syn_wbr S (syn_cfound) D) p0015
  have p0017 := @g_sopc D S
  have p0018 :=
    @g_sylib ph (syn_wbr S (syn_cstrict) D)
      (syn_wa (syn_wbr S (syn_cpartial) D) (syn_wbr S (syn_cconnex) D)) p0016 p0017
  have p0019 :=
    @g_simpld ph (syn_wbr S (syn_cpartial) D) (syn_wbr S (syn_cconnex) D) p0018
  have p0020 := @g_porta D S
  have p0021 :=
    @g_sylib ph (syn_wbr S (syn_cpartial) D)
      (syn_w3a (syn_wbr S (syn_cref) D) (syn_wbr S (syn_ctrans) D) (syn_wbr S (syn_cantisym) D))
      p0019 p0020
  have p0022 :=
    @g_simp1d ph (syn_wbr S (syn_cref) D) (syn_wbr S (syn_ctrans) D)
      (syn_wbr S (syn_cantisym) D) p0021
  have p0023 :=
    @g_syl (syn_wa ph (.classMem (.cv x) B)) ph (syn_wbr S (syn_cref) D) p0009 p0022
  have p0024 := @g_sselda ph B D (.cv x) hyp_werestrndv_2
  have p0025 := @g_refd (syn_wa ph (.classMem (.cv x) B)) D S (.cv x) p0023 p0024
  have p0026 := @g_simpr ph (.classMem (.cv x) B)
  have p0028 :=
    @g_jca (syn_wa ph (.classMem (.cv x) B)) (.classMem (.cv x) B) (.classMem (.cv x) B)
      p0026 p0026
  have p0029 := @g_brinxp (.cv x) (.cv x) B B S
  have p0030 :=
    @g_syl (syn_wa ph (.classMem (.cv x) B))
      (syn_wa (.classMem (.cv x) B) (.classMem (.cv x) B))
      (syn_wb (syn_wbr (.cv x) S (.cv x)) (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv x)))
      p0028 p0029
  have p0031 :=
    @g_mpbid (syn_wa ph (.classMem (.cv x) B)) (syn_wbr (.cv x) S (.cv x))
      (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv x)) p0025 p0030
  have p0032 :=
    @g_simp1 ph
      (syn_w3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B))
      (syn_wa (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y))
        (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv z)))
  have p0045 :=
    @g_simp2d ph (syn_wbr S (syn_cref) D) (syn_wbr S (syn_ctrans) D)
      (syn_wbr S (syn_cantisym) D) p0021
  have p0046 :=
    @g_syl
      (syn_w3a ph (syn_w3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B))
        (syn_wa (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y))
          (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv z))))
      ph (syn_wbr S (syn_ctrans) D) p0032 p0045
  have p0048 :=
    @g_syl
      (syn_w3a ph (syn_w3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B))
        (syn_wa (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y))
          (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv z))))
      ph (syn_wss B D) p0032 hyp_werestrndv_2
  have p0049 :=
    @g_simp2 ph
      (syn_w3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B))
      (syn_wa (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y))
        (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv z)))
  have p0050 := @g_simp1 (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B)
  have p0051 :=
    @g_syl
      (syn_w3a ph (syn_w3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B))
        (syn_wa (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y))
          (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv z))))
      (syn_w3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B))
      (.classMem (.cv x) B) p0049 p0050
  have p0052 :=
    @g_sseldd
      (syn_w3a ph (syn_w3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B))
        (syn_wa (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y))
          (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv z))))
      B D (.cv x) p0048 p0051
  have p0056 := @g_simp2 (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B)
  have p0057 :=
    @g_syl
      (syn_w3a ph (syn_w3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B))
        (syn_wa (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y))
          (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv z))))
      (syn_w3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B))
      (.classMem (.cv y) B) p0049 p0056
  have p0058 :=
    @g_sseldd
      (syn_w3a ph (syn_w3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B))
        (syn_wa (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y))
          (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv z))))
      B D (.cv y) p0048 p0057
  have p0062 := @g_simp3 (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B)
  have p0063 :=
    @g_syl
      (syn_w3a ph (syn_w3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B))
        (syn_wa (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y))
          (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv z))))
      (syn_w3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B))
      (.classMem (.cv z) B) p0049 p0062
  have p0064 :=
    @g_sseldd
      (syn_w3a ph (syn_w3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B))
        (syn_wa (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y))
          (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv z))))
      B D (.cv z) p0048 p0063
  have p0065 :=
    @g_simp3 ph
      (syn_w3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B))
      (syn_wa (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y))
        (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv z)))
  have p0066 :=
    @g_simpld
      (syn_w3a ph (syn_w3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B))
        (syn_wa (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y))
          (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv z))))
      (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y))
      (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv z)) p0065
  have p0067 := @g_brin (.cv x) (.cv y) S (syn_cxp B B)
  have p0068 :=
    @g_simplbi (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y))
      (syn_wbr (.cv x) S (.cv y)) (syn_wbr (.cv x) (syn_cxp B B) (.cv y)) p0067
  have p0069 :=
    @g_syl
      (syn_w3a ph (syn_w3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B))
        (syn_wa (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y))
          (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv z))))
      (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y)) (syn_wbr (.cv x) S (.cv y))
      p0066 p0068
  have p0071 :=
    @g_simprd
      (syn_w3a ph (syn_w3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B))
        (syn_wa (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y))
          (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv z))))
      (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y))
      (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv z)) p0065
  have p0072 := @g_brin (.cv y) (.cv z) S (syn_cxp B B)
  have p0073 :=
    @g_simplbi (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv z))
      (syn_wbr (.cv y) S (.cv z)) (syn_wbr (.cv y) (syn_cxp B B) (.cv z)) p0072
  have p0074 :=
    @g_syl
      (syn_w3a ph (syn_w3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B))
        (syn_wa (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y))
          (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv z))))
      (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv z)) (syn_wbr (.cv y) S (.cv z))
      p0071 p0073
  have p0075 :=
    @g_trd
      (syn_w3a ph (syn_w3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B))
        (syn_wa (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y))
          (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv z))))
      D S (.cv x) (.cv y) (.cv z) p0046 p0052 p0058 p0064 p0069 p0074
  have p0082 :=
    @g_jca
      (syn_w3a ph (syn_w3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B))
        (syn_wa (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y))
          (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv z))))
      (.classMem (.cv x) B) (.classMem (.cv z) B) p0051 p0063
  have p0083 := @g_brinxp (.cv x) (.cv z) B B S
  have p0084 :=
    @g_syl
      (syn_w3a ph (syn_w3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B))
        (syn_wa (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y))
          (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv z))))
      (syn_wa (.classMem (.cv x) B) (.classMem (.cv z) B))
      (syn_wb (syn_wbr (.cv x) S (.cv z)) (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv z)))
      p0082 p0083
  have p0085 :=
    @g_mpbid
      (syn_w3a ph (syn_w3a (.classMem (.cv x) B) (.classMem (.cv y) B) (.classMem (.cv z) B))
        (syn_wa (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y))
          (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv z))))
      (syn_wbr (.cv x) S (.cv z)) (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv z))
      p0075 p0084
  have p0086 :=
    @g_simp1 ph (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B))
      (syn_wa (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y))
        (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv x)))
  have p0099 :=
    @g_simp3d ph (syn_wbr S (syn_cref) D) (syn_wbr S (syn_ctrans) D)
      (syn_wbr S (syn_cantisym) D) p0021
  have p0100 :=
    @g_syl
      (syn_w3a ph (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B))
        (syn_wa (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y))
          (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv x))))
      ph (syn_wbr S (syn_cantisym) D) p0086 p0099
  have p0102 :=
    @g_syl
      (syn_w3a ph (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B))
        (syn_wa (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y))
          (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv x))))
      ph (syn_wss B D) p0086 hyp_werestrndv_2
  have p0103 :=
    @g_simp2 ph (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B))
      (syn_wa (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y))
        (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv x)))
  have p0104 :=
    @g_simpld
      (syn_w3a ph (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B))
        (syn_wa (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y))
          (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv x))))
      (.classMem (.cv x) B) (.classMem (.cv y) B) p0103
  have p0105 :=
    @g_sseldd
      (syn_w3a ph (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B))
        (syn_wa (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y))
          (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv x))))
      B D (.cv x) p0102 p0104
  have p0109 :=
    @g_simprd
      (syn_w3a ph (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B))
        (syn_wa (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y))
          (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv x))))
      (.classMem (.cv x) B) (.classMem (.cv y) B) p0103
  have p0110 :=
    @g_sseldd
      (syn_w3a ph (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B))
        (syn_wa (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y))
          (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv x))))
      B D (.cv y) p0102 p0109
  have p0111 :=
    @g_simp3 ph (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B))
      (syn_wa (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y))
        (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv x)))
  have p0112 :=
    @g_simpld
      (syn_w3a ph (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B))
        (syn_wa (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y))
          (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv x))))
      (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y))
      (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv x)) p0111
  have p0115 :=
    @g_syl
      (syn_w3a ph (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B))
        (syn_wa (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y))
          (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv x))))
      (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y)) (syn_wbr (.cv x) S (.cv y))
      p0112 p0068
  have p0117 :=
    @g_simprd
      (syn_w3a ph (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B))
        (syn_wa (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y))
          (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv x))))
      (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y))
      (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv x)) p0111
  have p0118 := @g_brin (.cv y) (.cv x) S (syn_cxp B B)
  have p0119 :=
    @g_simplbi (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv x))
      (syn_wbr (.cv y) S (.cv x)) (syn_wbr (.cv y) (syn_cxp B B) (.cv x)) p0118
  have p0120 :=
    @g_syl
      (syn_w3a ph (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B))
        (syn_wa (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y))
          (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv x))))
      (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv x)) (syn_wbr (.cv y) S (.cv x))
      p0117 p0119
  have p0121 :=
    @g_antid
      (syn_w3a ph (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B))
        (syn_wa (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y))
          (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv x))))
      D S (.cv x) (.cv y) p0100 p0105 p0110 p0115 p0120
  have p0122 := @g_simp1 ph (.classMem (.cv x) B) (.classMem (.cv y) B)
  have p0132 :=
    @g_simprd ph (syn_wbr S (syn_cpartial) D) (syn_wbr S (syn_cconnex) D) p0018
  have p0133 :=
    @g_syl (syn_w3a ph (.classMem (.cv x) B) (.classMem (.cv y) B)) ph
      (syn_wbr S (syn_cconnex) D) p0122 p0132
  have p0135 :=
    @g_syl (syn_w3a ph (.classMem (.cv x) B) (.classMem (.cv y) B)) ph (syn_wss B D) p0122
      hyp_werestrndv_2
  have p0136 := @g_simp2 ph (.classMem (.cv x) B) (.classMem (.cv y) B)
  have p0137 :=
    @g_sseldd (syn_w3a ph (.classMem (.cv x) B) (.classMem (.cv y) B)) B D (.cv x) p0135
      p0136
  have p0140 := @g_simp3 ph (.classMem (.cv x) B) (.classMem (.cv y) B)
  have p0141 :=
    @g_sseldd (syn_w3a ph (.classMem (.cv x) B) (.classMem (.cv y) B)) B D (.cv y) p0135
      p0140
  have p0142 :=
    @g_connexd (syn_w3a ph (.classMem (.cv x) B) (.classMem (.cv y) B)) D S (.cv x)
      (.cv y) p0133 p0137 p0141
  have p0145 :=
    @g_jca (syn_w3a ph (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classMem (.cv x) B)
      (.classMem (.cv y) B) p0136 p0140
  have p0146 := @g_brinxp (.cv x) (.cv y) B B S
  have p0147 :=
    @g_syl (syn_w3a ph (.classMem (.cv x) B) (.classMem (.cv y) B))
      (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B))
      (syn_wb (syn_wbr (.cv x) S (.cv y)) (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y)))
      p0145 p0146
  have p0150 :=
    @g_jca (syn_w3a ph (.classMem (.cv x) B) (.classMem (.cv y) B)) (.classMem (.cv y) B)
      (.classMem (.cv x) B) p0140 p0136
  have p0151 := @g_brinxp (.cv y) (.cv x) B B S
  have p0152 :=
    @g_syl (syn_w3a ph (.classMem (.cv x) B) (.classMem (.cv y) B))
      (syn_wa (.classMem (.cv y) B) (.classMem (.cv x) B))
      (syn_wb (syn_wbr (.cv y) S (.cv x)) (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv x)))
      p0150 p0151
  have p0153 :=
    @g_orbi12d (syn_w3a ph (.classMem (.cv x) B) (.classMem (.cv y) B))
      (syn_wbr (.cv x) S (.cv y)) (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y))
      (syn_wbr (.cv y) S (.cv x)) (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv x))
      p0147 p0152
  have p0154 :=
    @g_mpbid (syn_w3a ph (.classMem (.cv x) B) (.classMem (.cv y) B))
      (syn_wo (syn_wbr (.cv x) S (.cv y)) (syn_wbr (.cv y) S (.cv x)))
      (syn_wo (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y))
        (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv x)))
      p0142 p0153
  have p0155_e04_recanon :
    Nominal.NPrf
      (.imp (syn_w3a ph (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B))
          (syn_wa (syn_wbr (.cv x) (syn_cin S (syn_cxp B B)) (.cv y))
            (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv x)))) (.objEq x y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_w3a syn_wa
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0121
  have p0155 :=
    @g_sod ph x y z B (syn_cin S (syn_cxp B B)) (syn_cvv) (syn_cvv) dv_cache_0001
      dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
      dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 p0008
      hyp_werestrndv_3 p0031 p0085 p0155_e04_recanon p0154
  have p0165 := @g_simpl ph (syn_wa (syn_wss (.cv x) B) (syn_wne (.cv x) (syn_c0)))
  have p0166 := (Nominal.classEqRefl (syn_cwe))
  have p0167 := @g_breqi S D (syn_cwe) (syn_cin (syn_cstrict) (syn_cfound)) p0166
  have p0168 := @g_brin S D (syn_cstrict) (syn_cfound)
  have p0169 :=
    @g_bitri (syn_wbr S (syn_cwe) D) (syn_wbr S (syn_cin (syn_cstrict) (syn_cfound)) D)
      (syn_wa (syn_wbr S (syn_cstrict) D) (syn_wbr S (syn_cfound) D)) p0167 p0168
  have p0170 :=
    @g_biimpi (syn_wbr S (syn_cwe) D)
      (syn_wa (syn_wbr S (syn_cstrict) D) (syn_wbr S (syn_cfound) D)) p0169
  have p0171 :=
    @g_syl ph (syn_wbr S (syn_cwe) D)
      (syn_wa (syn_wbr S (syn_cstrict) D) (syn_wbr S (syn_cfound) D)) hyp_werestrndv_1
      p0170
  have p0172 := @g_simprd ph (syn_wbr S (syn_cstrict) D) (syn_wbr S (syn_cfound) D) p0171
  have p0173 :=
    @g_syl (syn_wa ph (syn_wa (syn_wss (.cv x) B) (syn_wne (.cv x) (syn_c0)))) ph
      (syn_wbr S (syn_cfound) D) p0165 p0172
  have p0174 := @g_vex x
  have p0175 :=
    @g_a1i (.classMem (.cv x) (syn_cvv))
      (syn_wa ph (syn_wa (syn_wss (.cv x) B) (syn_wne (.cv x) (syn_c0)))) p0174
  have p0176 := @g_simpr ph (syn_wa (syn_wss (.cv x) B) (syn_wne (.cv x) (syn_c0)))
  have p0177 :=
    @g_simpld (syn_wa ph (syn_wa (syn_wss (.cv x) B) (syn_wne (.cv x) (syn_c0))))
      (syn_wss (.cv x) B) (syn_wne (.cv x) (syn_c0)) p0176
  have p0178 := @g_simpl ph (syn_wa (syn_wss (.cv x) B) (syn_wne (.cv x) (syn_c0)))
  have p0179 :=
    @g_syl (syn_wa ph (syn_wa (syn_wss (.cv x) B) (syn_wne (.cv x) (syn_c0)))) ph
      (syn_wss B D) p0178 hyp_werestrndv_2
  have p0180 :=
    @g_sstrd (syn_wa ph (syn_wa (syn_wss (.cv x) B) (syn_wne (.cv x) (syn_c0)))) (.cv x) B
      D p0177 p0179
  have p0181 := @g_simpr ph (syn_wa (syn_wss (.cv x) B) (syn_wne (.cv x) (syn_c0)))
  have p0182 :=
    @g_simprd (syn_wa ph (syn_wa (syn_wss (.cv x) B) (syn_wne (.cv x) (syn_c0))))
      (syn_wss (.cv x) B) (syn_wne (.cv x) (syn_c0)) p0181
  have p0183 :=
    @g_frd (syn_wa ph (syn_wa (syn_wss (.cv x) B) (syn_wne (.cv x) (syn_c0)))) z y D S
      (syn_cvv) (.cv x) dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
      dv_cache_0017 p0173 p0175 p0180 p0182
  have p0184 := @g_brin (.cv y) (.cv z) S (syn_cxp B B)
  have p0185 :=
    @g_simplbi (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv z))
      (syn_wbr (.cv y) S (.cv z)) (syn_wbr (.cv y) (syn_cxp B B) (.cv z)) p0184
  have p0186 :=
    @g_imim1i (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv z))
      (syn_wbr (.cv y) S (.cv z)) (.classEq (.cv y) (.cv z)) p0185
  have p0187 :=
    @g_a1i
      (.imp (.imp (syn_wbr (.cv y) S (.cv z)) (.classEq (.cv y) (.cv z)))
        (.imp (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv z)) (.classEq (.cv y) (.cv z))))
      (syn_wa ph (syn_wa (syn_wss (.cv x) B) (syn_wne (.cv x) (syn_c0)))) p0186
  have p0188 :=
    @g_ralimdv (syn_wa ph (syn_wa (syn_wss (.cv x) B) (syn_wne (.cv x) (syn_c0))))
      (.imp (syn_wbr (.cv y) S (.cv z)) (.classEq (.cv y) (.cv z)))
      (.imp (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv z)) (.classEq (.cv y) (.cv z)))
      y (.cv x) dv_cache_0018 p0187
  have p0189 :=
    @g_reximdv (syn_wa ph (syn_wa (syn_wss (.cv x) B) (syn_wne (.cv x) (syn_c0))))
      (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) S (.cv z)) (.classEq (.cv y) (.cv z))))
      (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv z))
          (.classEq (.cv y) (.cv z))))
      z (.cv x) dv_cache_0019 p0188
  have p0190_e00_recanon :
    Nominal.NPrf
      (.imp (syn_wa ph (syn_wa (syn_wss (.cv x) B) (syn_wne (.cv x) (syn_c0))))
        (syn_wrex z (.cv x) (syn_wral y (.cv x)
            (.imp (syn_wbr (.cv y) S (.cv z)) (.classEq (.cv y) (.cv z)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_wrex syn_wex syn_wral syn_wbr syn_cop syn_cun syn_cnin syn_wnan
          syn_ccompl
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.all
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _)
      p0183
  have p0190 :=
    @g_mpd (syn_wa ph (syn_wa (syn_wss (.cv x) B) (syn_wne (.cv x) (syn_c0))))
      (syn_wrex z (.cv x) (syn_wral y (.cv x)
          (.imp (syn_wbr (.cv y) S (.cv z)) (.classEq (.cv y) (.cv z)))))
      (syn_wrex z (.cv x) (syn_wral y (.cv x)
          (.imp (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv z))
            (.classEq (.cv y) (.cv z)))))
      p0190_e00_recanon p0189
  have p0191_e02_recanon :
    Nominal.NPrf
      (.imp (syn_wa ph (syn_wa (syn_wss (.cv x) B) (syn_wne (.cv x) (syn_c0))))
        (syn_wrex z (.cv x) (syn_wral y (.cv x)
            (.imp (syn_wbr (.cv y) (syn_cin S (syn_cxp B B)) (.cv z)) (.objEq y z))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_wrex syn_wex syn_wral syn_wbr syn_cop syn_cun syn_cnin syn_wnan
          syn_ccompl syn_cin syn_cxp syn_copab
        simp (config :=
          {
            failIfUnchanged :=
              false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.all
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0190
  have p0191 :=
    @g_frrd ph x y z B (syn_cin S (syn_cxp B B)) dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0010 dv_cache_0011
      dv_cache_0012 p0008 hyp_werestrndv_3 p0191_e02_recanon
  have p0192 :=
    @g_jca ph (syn_wbr (syn_cin S (syn_cxp B B)) (syn_cstrict) B)
      (syn_wbr (syn_cin S (syn_cxp B B)) (syn_cfound) B) p0155 p0191
  have p0194 :=
    @g_breqi (syn_cin S (syn_cxp B B)) B (syn_cwe) (syn_cin (syn_cstrict) (syn_cfound))
      p0010
  have p0195 := @g_brin (syn_cin S (syn_cxp B B)) B (syn_cstrict) (syn_cfound)
  have p0196 :=
    @g_bitri (syn_wbr (syn_cin S (syn_cxp B B)) (syn_cwe) B)
      (syn_wbr (syn_cin S (syn_cxp B B)) (syn_cin (syn_cstrict) (syn_cfound)) B)
      (syn_wa (syn_wbr (syn_cin S (syn_cxp B B)) (syn_cstrict) B)
        (syn_wbr (syn_cin S (syn_cxp B B)) (syn_cfound) B))
      p0194 p0195
  have p0197 :=
    @g_a1i
      (syn_wb (syn_wbr (syn_cin S (syn_cxp B B)) (syn_cwe) B)
        (syn_wa (syn_wbr (syn_cin S (syn_cxp B B)) (syn_cstrict) B)
          (syn_wbr (syn_cin S (syn_cxp B B)) (syn_cfound) B)))
      ph p0196
  have p0198 :=
    @g_mpbird ph (syn_wbr (syn_cin S (syn_cxp B B)) (syn_cwe) B)
      (syn_wa (syn_wbr (syn_cin S (syn_cxp B B)) (syn_cstrict) B)
        (syn_wbr (syn_cin S (syn_cxp B B)) (syn_cfound) B))
      p0192 p0197
  exact p0198

@[expose]
noncomputable def g_westrseg (x : Var) (D : Class) (R : Class)
    (dv_D_R : Disjoint D.fv R.fv) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wbr (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cwe)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) :=
  by
  have dv_cache_0001 : Disjoint (D).fv (R).fv := by
    exact
      (show Disjoint (D).fv (R).fv from (show Disjoint (D).fv (R).fv from (by exact dv_D_R)))
  have p0000 := @g_simpl (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)
  have p0001 := @g_inss1 D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))
  have p0002 :=
    @g_a1i
      (syn_wss (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) D)
      (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) p0001
  have p0004 := @g_brex R D (syn_cwe)
  have p0005 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wbr R (syn_cwe) D)
      (syn_wa (.classMem R (syn_cvv)) (.classMem D (syn_cvv))) p0000 p0004
  have p0006 :=
    @g_simprd (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D))
      (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0005
  have p0010 :=
    @g_simpld (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D))
      (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0005
  have p0011 := @g_idex
  have p0012 :=
    @g_a1i (.classMem (syn_cid) (syn_cvv))
      (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) p0011
  have p0013 :=
    @g_jca (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem R (syn_cvv))
      (.classMem (syn_cid) (syn_cvv)) p0010 p0012
  have p0014 := @g_difexg R (syn_cid) (syn_cvv) (syn_cvv)
  have p0015 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D))
      (syn_wa (.classMem R (syn_cvv)) (.classMem (syn_cid) (syn_cvv)))
      (.classMem (syn_cdif R (syn_cid)) (syn_cvv)) p0013 p0014
  have p0016 := @g_cnvexg (syn_cdif R (syn_cid)) (syn_cvv)
  have p0017 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D))
      (.classMem (syn_cdif R (syn_cid)) (syn_cvv))
      (.classMem (syn_ccnv (syn_cdif R (syn_cid))) (syn_cvv)) p0015 p0016
  have p0018 := @g_snex (.cv x)
  have p0019 :=
    @g_a1i (.classMem (syn_csn (.cv x)) (syn_cvv))
      (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) p0018
  have p0020 :=
    @g_jca (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D))
      (.classMem (syn_ccnv (syn_cdif R (syn_cid))) (syn_cvv))
      (.classMem (syn_csn (.cv x)) (syn_cvv)) p0017 p0019
  have p0021 :=
    @g_imaexg (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)) (syn_cvv) (syn_cvv)
  have p0022 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D))
      (syn_wa (.classMem (syn_ccnv (syn_cdif R (syn_cid))) (syn_cvv))
        (.classMem (syn_csn (.cv x)) (syn_cvv)))
      (.classMem (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) (syn_cvv))
      p0020 p0021
  have p0023 :=
    @g_jca (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem D (syn_cvv))
      (.classMem (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) (syn_cvv))
      p0006 p0022
  have p0024 :=
    @g_inexg D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) (syn_cvv)
      (syn_cvv)
  have p0025 :=
    @g_syl (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D))
      (syn_wa (.classMem D (syn_cvv))
        (.classMem (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) (syn_cvv)))
      (.classMem (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cvv))
      p0023 p0024
  have p0026 :=
    @g_werestr (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) D
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) R
      dv_cache_0001 p0000 p0002 p0025
  exact p0026

@[expose]
noncomputable def g_westrsegndv (x : Var) (D : Class) (S : Class) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wbr S (syn_cwe) D) (.classMem (.cv x) D)) (syn_wbr (syn_cin S (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))
          (syn_cwe)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) :=
  by
  have p0000 := @g_simpl (syn_wbr S (syn_cwe) D) (.classMem (.cv x) D)
  have p0001 := @g_inss1 D (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))
  have p0002 :=
    @g_a1i
      (syn_wss (syn_cin D (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) D)
      (syn_wa (syn_wbr S (syn_cwe) D) (.classMem (.cv x) D)) p0001
  have p0004 := @g_brex S D (syn_cwe)
  have p0005 :=
    @g_syl (syn_wa (syn_wbr S (syn_cwe) D) (.classMem (.cv x) D)) (syn_wbr S (syn_cwe) D)
      (syn_wa (.classMem S (syn_cvv)) (.classMem D (syn_cvv))) p0000 p0004
  have p0006 :=
    @g_simprd (syn_wa (syn_wbr S (syn_cwe) D) (.classMem (.cv x) D))
      (.classMem S (syn_cvv)) (.classMem D (syn_cvv)) p0005
  have p0010 :=
    @g_simpld (syn_wa (syn_wbr S (syn_cwe) D) (.classMem (.cv x) D))
      (.classMem S (syn_cvv)) (.classMem D (syn_cvv)) p0005
  have p0011 := @g_idex
  have p0012 :=
    @g_a1i (.classMem (syn_cid) (syn_cvv))
      (syn_wa (syn_wbr S (syn_cwe) D) (.classMem (.cv x) D)) p0011
  have p0013 :=
    @g_jca (syn_wa (syn_wbr S (syn_cwe) D) (.classMem (.cv x) D)) (.classMem S (syn_cvv))
      (.classMem (syn_cid) (syn_cvv)) p0010 p0012
  have p0014 := @g_difexg S (syn_cid) (syn_cvv) (syn_cvv)
  have p0015 :=
    @g_syl (syn_wa (syn_wbr S (syn_cwe) D) (.classMem (.cv x) D))
      (syn_wa (.classMem S (syn_cvv)) (.classMem (syn_cid) (syn_cvv)))
      (.classMem (syn_cdif S (syn_cid)) (syn_cvv)) p0013 p0014
  have p0016 := @g_cnvexg (syn_cdif S (syn_cid)) (syn_cvv)
  have p0017 :=
    @g_syl (syn_wa (syn_wbr S (syn_cwe) D) (.classMem (.cv x) D))
      (.classMem (syn_cdif S (syn_cid)) (syn_cvv))
      (.classMem (syn_ccnv (syn_cdif S (syn_cid))) (syn_cvv)) p0015 p0016
  have p0018 := @g_snex (.cv x)
  have p0019 :=
    @g_a1i (.classMem (syn_csn (.cv x)) (syn_cvv))
      (syn_wa (syn_wbr S (syn_cwe) D) (.classMem (.cv x) D)) p0018
  have p0020 :=
    @g_jca (syn_wa (syn_wbr S (syn_cwe) D) (.classMem (.cv x) D))
      (.classMem (syn_ccnv (syn_cdif S (syn_cid))) (syn_cvv))
      (.classMem (syn_csn (.cv x)) (syn_cvv)) p0017 p0019
  have p0021 :=
    @g_imaexg (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)) (syn_cvv) (syn_cvv)
  have p0022 :=
    @g_syl (syn_wa (syn_wbr S (syn_cwe) D) (.classMem (.cv x) D))
      (syn_wa (.classMem (syn_ccnv (syn_cdif S (syn_cid))) (syn_cvv))
        (.classMem (syn_csn (.cv x)) (syn_cvv)))
      (.classMem (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))) (syn_cvv))
      p0020 p0021
  have p0023 :=
    @g_jca (syn_wa (syn_wbr S (syn_cwe) D) (.classMem (.cv x) D)) (.classMem D (syn_cvv))
      (.classMem (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))) (syn_cvv))
      p0006 p0022
  have p0024 :=
    @g_inexg D (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))) (syn_cvv)
      (syn_cvv)
  have p0025 :=
    @g_syl (syn_wa (syn_wbr S (syn_cwe) D) (.classMem (.cv x) D))
      (syn_wa (.classMem D (syn_cvv))
        (.classMem (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))) (syn_cvv)))
      (.classMem (syn_cin D (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))
        (syn_cvv))
      p0023 p0024
  have p0026 :=
    @g_werestrndv (syn_wa (syn_wbr S (syn_cwe) D) (.classMem (.cv x) D))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) D S p0000
      p0002 p0025
  exact p0026

@[expose]
noncomputable def g_strictsegnel (x : Var) (D : Class) (R : Class) :
    Nominal.NPrf
      (.neg (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) :=
  by
  have p0000 := @g_eqid (.cv x)
  have p0001 := @g_vex x
  have p0002 := @g_ideq (.cv x) (.cv x) p0001
  have p0003 :=
    @g_mpbir (syn_wbr (.cv x) (syn_cid) (.cv x)) (.classEq (.cv x) (.cv x)) p0000 p0002
  have p0004 := @g_notnoti (syn_wbr (.cv x) (syn_cid) (.cv x)) p0003
  have p0005 :=
    @g_intnan (.neg (syn_wbr (.cv x) (syn_cid) (.cv x))) (syn_wbr (.cv x) R (.cv x)) p0004
  have p0006 := @g_brdif (.cv x) (.cv x) R (syn_cid)
  have p0007 :=
    @g_mtbir (syn_wbr (.cv x) (syn_cdif R (syn_cid)) (.cv x))
      (syn_wa (syn_wbr (.cv x) R (.cv x)) (.neg (syn_wbr (.cv x) (syn_cid) (.cv x))))
      p0005 p0006
  have p0008 := @g_eliniseg (syn_cdif R (syn_cid)) (.cv x) (.cv x)
  have p0009 :=
    @g_mtbir
      (.classMem (.cv x) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_wbr (.cv x) (syn_cdif R (syn_cid)) (.cv x)) p0007 p0008
  have p0010 :=
    @g_intnan
      (.classMem (.cv x) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (.classMem (.cv x) D) p0009
  have p0011 :=
    @g_elin (.cv x) D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))
  have p0012 :=
    @g_mtbir
      (.classMem (.cv x)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (syn_wa (.classMem (.cv x) D) (.classMem (.cv x)
          (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      p0010 p0011
  exact p0012


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk014Compact001Part045`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_elstrictseg (x : Var) (y : Var) (D : Class) (R : Class) :
    Nominal.NPrf
      (syn_wb (.classMem (.cv y)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
        (syn_wa (.classMem (.cv y) D)
          (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x))))) :=
  by
  have p0000 :=
    @g_elin (.cv y) D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))
  have p0001 := @g_eliniseg (syn_cdif R (syn_cid)) (.cv x) (.cv y)
  have p0002 := @g_brdif (.cv y) (.cv x) R (syn_cid)
  have p0003 := @g_vex x
  have p0004 := @g_ideq (.cv y) (.cv x) p0003
  have p0005 :=
    @g_notbii (syn_wbr (.cv y) (syn_cid) (.cv x)) (.classEq (.cv y) (.cv x)) p0004
  have p0006 := (Nominal.biimpRefl (syn_wne (.cv y) (.cv x)))
  have p0007 :=
    @g_bitr4i (.neg (syn_wbr (.cv y) (syn_cid) (.cv x))) (.neg (.classEq (.cv y) (.cv x)))
      (syn_wne (.cv y) (.cv x)) p0005 p0006
  have p0008 :=
    @g_anbi2i (.neg (syn_wbr (.cv y) (syn_cid) (.cv x))) (syn_wne (.cv y) (.cv x))
      (syn_wbr (.cv y) R (.cv x)) p0007
  have p0009 :=
    @g_bitri (syn_wbr (.cv y) (syn_cdif R (syn_cid)) (.cv x))
      (syn_wa (syn_wbr (.cv y) R (.cv x)) (.neg (syn_wbr (.cv y) (syn_cid) (.cv x))))
      (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x))) p0002 p0008
  have p0010 :=
    @g_bitri
      (.classMem (.cv y) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_wbr (.cv y) (syn_cdif R (syn_cid)) (.cv x))
      (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x))) p0001 p0009
  have p0011 :=
    @g_anbi2i
      (.classMem (.cv y) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x))) (.classMem (.cv y) D)
      p0010
  have p0012 :=
    @g_bitri
      (.classMem (.cv y)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (syn_wa (.classMem (.cv y) D) (.classMem (.cv y)
          (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (syn_wa (.classMem (.cv y) D)
        (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x))))
      p0000 p0011
  exact p0012

@[expose]
noncomputable def g_strictsegdown (x : Var) (y : Var) (z : Var) (D : Class) (R : Class) :
    Nominal.NPrf
      (.imp (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa
            (.classMem (.cv y)
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
            (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y))) (.classMem (.cv z)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) :=
  by
  have p0000 :=
    @g_simp2 (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D))
      (syn_wa (.classMem (.cv y)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
        (.classMem (.cv z) D))
      (syn_wbr (.cv z) R (.cv y))
  have p0001 :=
    @g_simprd
      (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y)))
      (.classMem (.cv y)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (.classMem (.cv z) D) p0000
  have p0002 :=
    @g_simp1 (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D))
      (syn_wa (.classMem (.cv y)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
        (.classMem (.cv z) D))
      (syn_wbr (.cv z) R (.cv y))
  have p0003 :=
    @g_simpld
      (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y)))
      (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D) p0002
  have p0004 := (Nominal.classEqRefl (syn_cwe))
  have p0005 := @g_breqi R D (syn_cwe) (syn_cin (syn_cstrict) (syn_cfound)) p0004
  have p0006 := @g_brin R D (syn_cstrict) (syn_cfound)
  have p0007 :=
    @g_bitri (syn_wbr R (syn_cwe) D) (syn_wbr R (syn_cin (syn_cstrict) (syn_cfound)) D)
      (syn_wa (syn_wbr R (syn_cstrict) D) (syn_wbr R (syn_cfound) D)) p0005 p0006
  have p0008 :=
    @g_biimpi (syn_wbr R (syn_cwe) D)
      (syn_wa (syn_wbr R (syn_cstrict) D) (syn_wbr R (syn_cfound) D)) p0007
  have p0009 :=
    @g_syl
      (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y)))
      (syn_wbr R (syn_cwe) D)
      (syn_wa (syn_wbr R (syn_cstrict) D) (syn_wbr R (syn_cfound) D)) p0003 p0008
  have p0010 :=
    @g_simpld
      (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y)))
      (syn_wbr R (syn_cstrict) D) (syn_wbr R (syn_cfound) D) p0009
  have p0011 := @g_sopc D R
  have p0012 :=
    @g_sylib
      (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y)))
      (syn_wbr R (syn_cstrict) D)
      (syn_wa (syn_wbr R (syn_cpartial) D) (syn_wbr R (syn_cconnex) D)) p0010 p0011
  have p0013 :=
    @g_simpld
      (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y)))
      (syn_wbr R (syn_cpartial) D) (syn_wbr R (syn_cconnex) D) p0012
  have p0014 := @g_porta D R
  have p0015 :=
    @g_sylib
      (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y)))
      (syn_wbr R (syn_cpartial) D)
      (syn_w3a (syn_wbr R (syn_cref) D) (syn_wbr R (syn_ctrans) D) (syn_wbr R (syn_cantisym) D))
      p0013 p0014
  have p0016 :=
    @g_simp2d
      (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y)))
      (syn_wbr R (syn_cref) D) (syn_wbr R (syn_ctrans) D) (syn_wbr R (syn_cantisym) D)
      p0015
  have p0020 :=
    @g_simpld
      (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y)))
      (.classMem (.cv y)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (.classMem (.cv z) D) p0000
  have p0021 :=
    @g_elin (.cv y) D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))
  have p0022 := @g_eliniseg (syn_cdif R (syn_cid)) (.cv x) (.cv y)
  have p0023 := @g_brdif (.cv y) (.cv x) R (syn_cid)
  have p0024 := @g_vex x
  have p0025 := @g_ideq (.cv y) (.cv x) p0024
  have p0026 :=
    @g_notbii (syn_wbr (.cv y) (syn_cid) (.cv x)) (.classEq (.cv y) (.cv x)) p0025
  have p0027 := (Nominal.biimpRefl (syn_wne (.cv y) (.cv x)))
  have p0028 :=
    @g_bitr4i (.neg (syn_wbr (.cv y) (syn_cid) (.cv x))) (.neg (.classEq (.cv y) (.cv x)))
      (syn_wne (.cv y) (.cv x)) p0026 p0027
  have p0029 :=
    @g_anbi2i (.neg (syn_wbr (.cv y) (syn_cid) (.cv x))) (syn_wne (.cv y) (.cv x))
      (syn_wbr (.cv y) R (.cv x)) p0028
  have p0030 :=
    @g_bitri (syn_wbr (.cv y) (syn_cdif R (syn_cid)) (.cv x))
      (syn_wa (syn_wbr (.cv y) R (.cv x)) (.neg (syn_wbr (.cv y) (syn_cid) (.cv x))))
      (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x))) p0023 p0029
  have p0031 :=
    @g_bitri
      (.classMem (.cv y) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_wbr (.cv y) (syn_cdif R (syn_cid)) (.cv x))
      (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x))) p0022 p0030
  have p0032 :=
    @g_anbi2i
      (.classMem (.cv y) (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x))) (.classMem (.cv y) D)
      p0031
  have p0033 :=
    @g_bitri
      (.classMem (.cv y)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (syn_wa (.classMem (.cv y) D) (.classMem (.cv y)
          (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (syn_wa (.classMem (.cv y) D)
        (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x))))
      p0021 p0032
  have p0034 :=
    @g_biimpi
      (.classMem (.cv y)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (syn_wa (.classMem (.cv y) D)
        (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x))))
      p0033
  have p0035 :=
    @g_syl
      (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y)))
      (.classMem (.cv y)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (syn_wa (.classMem (.cv y) D)
        (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x))))
      p0020 p0034
  have p0036 :=
    @g_simpld
      (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y)))
      (.classMem (.cv y) D) (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x)))
      p0035
  have p0038 :=
    @g_simprd
      (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y)))
      (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D) p0002
  have p0039 :=
    @g_simp3 (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D))
      (syn_wa (.classMem (.cv y)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
        (.classMem (.cv z) D))
      (syn_wbr (.cv z) R (.cv y))
  have p0057 :=
    @g_simprd
      (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y)))
      (.classMem (.cv y) D) (syn_wa (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x)))
      p0035
  have p0058 :=
    @g_simpld
      (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y)))
      (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x)) p0057
  have p0059 :=
    @g_trd
      (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y)))
      D R (.cv z) (.cv y) (.cv x) p0016 p0001 p0036 p0038 p0039 p0058
  have p0078 :=
    @g_simprd
      (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y)))
      (syn_wbr (.cv y) R (.cv x)) (syn_wne (.cv y) (.cv x)) p0057
  have p0079 :=
    @g_simpl
      (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y)))
      (.classEq (.cv z) (.cv x))
  have p0094 :=
    @g_simp3d
      (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y)))
      (syn_wbr R (syn_cref) D) (syn_wbr R (syn_ctrans) D) (syn_wbr R (syn_cantisym) D)
      p0015
  have p0095 :=
    @g_syl
      (syn_wa (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa
            (.classMem (.cv y)
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
            (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y))) (.classEq (.cv z) (.cv x)))
      (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y)))
      (syn_wbr R (syn_cantisym) D) p0079 p0094
  have p0099 :=
    @g_syl
      (syn_wa (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa
            (.classMem (.cv y)
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
            (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y))) (.classEq (.cv z) (.cv x)))
      (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y)))
      (.classMem (.cv x) D) p0079 p0038
  have p0119 :=
    @g_syl
      (syn_wa (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa
            (.classMem (.cv y)
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
            (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y))) (.classEq (.cv z) (.cv x)))
      (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y)))
      (.classMem (.cv y) D) p0079 p0036
  have p0120 :=
    @g_simpr
      (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y)))
      (.classEq (.cv z) (.cv x))
  have p0123 :=
    @g_syl
      (syn_wa (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa
            (.classMem (.cv y)
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
            (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y))) (.classEq (.cv z) (.cv x)))
      (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y)))
      (syn_wbr (.cv z) R (.cv y)) p0079 p0039
  have p0124 :=
    @g_eqbrtrrd
      (syn_wa (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa
            (.classMem (.cv y)
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
            (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y))) (.classEq (.cv z) (.cv x)))
      (.cv z) (.cv x) (.cv y) R p0120 p0123
  have p0145 :=
    @g_syl
      (syn_wa (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa
            (.classMem (.cv y)
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
            (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y))) (.classEq (.cv z) (.cv x)))
      (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y)))
      (syn_wbr (.cv y) R (.cv x)) p0079 p0058
  have p0146 :=
    @g_antid
      (syn_wa (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa
            (.classMem (.cv y)
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
            (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y))) (.classEq (.cv z) (.cv x)))
      D R (.cv x) (.cv y) p0095 p0099 p0119 p0124 p0145
  have p0147 :=
    @g_eqcomd
      (syn_wa (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa
            (.classMem (.cv y)
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
            (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y))) (.classEq (.cv z) (.cv x)))
      (.cv x) (.cv y) p0146
  have p0149 :=
    @g_biimpi (syn_wne (.cv y) (.cv x)) (.neg (.classEq (.cv y) (.cv x))) p0027
  have p0150 :=
    @g_a1i (.imp (syn_wne (.cv y) (.cv x)) (.neg (.classEq (.cv y) (.cv x))))
      (syn_wa (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa
            (.classMem (.cv y)
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
            (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y))) (.classEq (.cv z) (.cv x)))
      p0149
  have p0151 :=
    @g_mt2d
      (syn_wa (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa
            (.classMem (.cv y)
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
            (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y))) (.classEq (.cv z) (.cv x)))
      (syn_wne (.cv y) (.cv x)) (.classEq (.cv y) (.cv x)) p0147 p0150
  have p0152 :=
    @g_ex
      (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y)))
      (.classEq (.cv z) (.cv x)) (.neg (syn_wne (.cv y) (.cv x))) p0151
  have p0153 :=
    @g_necon2ad
      (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y)))
      (syn_wne (.cv y) (.cv x)) (.cv z) (.cv x) p0152
  have p0154 :=
    @g_mpd
      (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y)))
      (syn_wne (.cv y) (.cv x)) (syn_wne (.cv z) (.cv x)) p0078 p0153
  have p0155 :=
    @g_jca
      (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y)))
      (syn_wbr (.cv z) R (.cv x)) (syn_wne (.cv z) (.cv x)) p0059 p0154
  have p0156 :=
    @g_jca
      (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y)))
      (.classMem (.cv z) D) (syn_wa (syn_wbr (.cv z) R (.cv x)) (syn_wne (.cv z) (.cv x)))
      p0001 p0155
  have p0157 := @g_elstrictseg x z D R
  have p0158 :=
    @g_biimpri
      (.classMem (.cv z)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (syn_wa (.classMem (.cv z) D)
        (syn_wa (syn_wbr (.cv z) R (.cv x)) (syn_wne (.cv z) (.cv x))))
      p0157
  have p0159 :=
    @g_syl
      (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (syn_wa (.classMem (.cv y)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv y)))
      (syn_wa (.classMem (.cv z) D)
        (syn_wa (syn_wbr (.cv z) R (.cv x)) (syn_wne (.cv z) (.cv x))))
      (.classMem (.cv z)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      p0156 p0158
  exact p0159


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk014Compact001Part046`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_strictsegnoiso (x : Var) (D : Class) (R : Class) (H : Class) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D))
          (.classMem H (syn_cvv))) (.neg (syn_wiso H R (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ D.fv ∪ R.fv ∪ H.fv
  let z : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let w : Var := freshVar proofSupport 2
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_not_D : z ∉ D.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_not_R : z ∉ R.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_H : z ∉ H.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_y_not_D : y ∉ D.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_H : y ∉ H.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_w_not_D : w ∉ D.fv := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_w_not_R : w ∉ R.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_w_not_H : w ∉ H.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have fresh_z_ne_y : z ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_z : y ≠ z := Ne.symm fresh_z_ne_y
  have fresh_y_ne_w : y ≠ w :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_w_ne_y : w ≠ y := Ne.symm fresh_y_ne_w
  have dv_cache_0001 : w ∉ ((Class.cv x)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_w_ne_x, not_false_eq_true])
  have dv_cache_0002 : w ∉ ((syn_cin H R)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, Finset.mem_union,
          fresh_w_not_H, fresh_w_not_R, or_false, not_false_eq_true])
  have dv_cache_0003 : w ∉ ((syn_wa (syn_wfn H D) (.classMem (.cv x) D))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfn,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_w_not_H, fresh_w_not_D, fresh_w_ne_x, or_false,
          not_false_eq_true])
  have dv_cache_0004 : w ∉ ((syn_cfv H (.cv x))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_x, fresh_w_not_H, or_false, not_false_eq_true])
  have dv_cache_0005 : w ∉ ((syn_wbr (.cv x) R (syn_cfv H (.cv x)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_x, fresh_w_not_H, fresh_w_not_R, or_false,
          not_false_eq_true])
  have dv_cache_0006 : y ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_R, not_false_eq_true])
  have dv_cache_0007 : z ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_R, not_false_eq_true])
  have dv_cache_0008 : y ∉ ((syn_cdif D (syn_cdm (syn_cin H R)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, Finset.mem_union,
          fresh_y_not_D, fresh_y_not_H, fresh_y_not_R, or_false, not_false_eq_true])
  have dv_cache_0009 : z ∉ ((syn_cdif D (syn_cdm (syn_cin H R)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, Finset.mem_union,
          fresh_z_not_D, fresh_z_not_H, fresh_z_not_R, or_false, not_false_eq_true])
  have dv_cache_0010 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0011 : w ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_w_ne_y, not_false_eq_true])
  have dv_cache_0012 : w ∉ ((syn_wa (syn_wfn H D) (.classMem (.cv y) D))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfn,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_w_not_H, fresh_w_not_D, fresh_w_ne_y, or_false,
          not_false_eq_true])
  have dv_cache_0013 : w ∉ ((syn_cfv H (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_y, fresh_w_not_H, or_false, not_false_eq_true])
  have dv_cache_0014 : w ∉ ((syn_wbr (.cv y) R (syn_cfv H (.cv y)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_y, fresh_w_not_H, fresh_w_not_R, or_false,
          not_false_eq_true])
  have dv_cache_0015 : z ∉ ((syn_cfv H (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_y, fresh_z_not_H, or_false, not_false_eq_true])
  have dv_cache_0016 :
    z ∉
      ((Wff.imp (syn_wbr (syn_cfv H (.cv y)) R (.cv y))
          (.classEq (syn_cfv H (.cv y)) (.cv y)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_y, fresh_z_not_H, fresh_z_not_R, or_false,
          not_false_eq_true])
  have dv_cache_0017 :
    w ∉ ((syn_wa (syn_wfn H D) (.classMem (syn_cfv H (.cv y)) D))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfn,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_w_not_H, fresh_w_not_D, fresh_w_ne_y, or_false,
          not_false_eq_true])
  have dv_cache_0018 : w ∉ ((syn_cfv H (syn_cfv H (.cv y)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_y, fresh_w_not_H, or_false, not_false_eq_true])
  have dv_cache_0019 :
    w ∉ ((syn_wbr (syn_cfv H (.cv y)) R (syn_cfv H (syn_cfv H (.cv y))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_y, fresh_w_not_H, fresh_w_not_R, or_false,
          not_false_eq_true])
  have dv_cache_0020 :
    y ∉
      ((Wff.neg (syn_wiso H R (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_not_D, fresh_y_not_R, fresh_y_ne_x, fresh_y_not_H,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0021 :
    y ∉
      ((syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D))
            (.classMem H (syn_cvv))) (syn_wiso H R (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) D
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_y_not_R, fresh_y_not_D, fresh_y_ne_x, fresh_y_not_H,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  let syntaxFormula0000 : Wff :=
    (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) (.classMem H (syn_cvv)))
  let syntaxClass0001 : Class :=
    (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  let syntaxClass0002 : Class := (syn_cin R syntaxClass0001)
  let syntaxFormula0003 : Wff :=
    (syn_wiso H R syntaxClass0002 D
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  let syntaxFormula0004 : Wff := (syn_wa syntaxFormula0000 syntaxFormula0003)
  let syntaxFormula0005 : Wff :=
    (syn_wa syntaxFormula0004 (syn_wbr (.cv x) R (syn_cfv H (.cv x))))
  let syntaxFormula0006 : Wff :=
    (syn_wf1o H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  let syntaxFormula0007 : Wff :=
    (syn_wf H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  let syntaxFormula0008 : Wff := (syn_wa syntaxFormula0007 (.classMem (.cv x) D))
  let syntaxFormula0009 : Wff :=
    (.classMem (syn_cfv H (.cv x))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  let syntaxFormula0010 : Wff :=
    (syn_wa (syn_wbr (syn_cfv H (.cv x)) R (.cv x))
      (.neg (syn_wbr (syn_cfv H (.cv x)) (syn_cid) (.cv x))))
  let syntaxFormula0011 : Wff :=
    (syn_wa (syn_wbr (syn_cfv H (.cv x)) R (.cv x)) (syn_wne (syn_cfv H (.cv x)) (.cv x)))
  let syntaxFormula0012 : Wff :=
    (.classMem (syn_cfv H (.cv x))
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
  let syntaxFormula0013 : Wff :=
    (syn_wa (.classMem (syn_cfv H (.cv x)) D) syntaxFormula0012)
  let syntaxFormula0014 : Wff :=
    (syn_wa (.classMem (syn_cfv H (.cv x)) D) syntaxFormula0011)
  let syntaxFormula0015 : Wff :=
    (syn_wex w (syn_wa (.classEq (.cv w) (syn_cfv H (.cv x))) (syn_wbr (.cv x) R (.cv w))))
  let syntaxFormula0016 : Wff :=
    (syn_wral z (syn_cdif D (syn_cdm (syn_cin H R)))
      (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y))))
  let syntaxFormula0017 : Wff :=
    (syn_w3a syntaxFormula0004 (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R))))
      syntaxFormula0016)
  let syntaxFormula0018 : Wff := (syn_wa syntaxFormula0007 (.classMem (.cv y) D))
  let syntaxFormula0019 : Wff :=
    (.classMem (syn_cfv H (.cv y))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  let syntaxFormula0020 : Wff :=
    (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x))
      (.neg (syn_wbr (syn_cfv H (.cv y)) (syn_cid) (.cv x))))
  let syntaxFormula0021 : Wff :=
    (syn_wa (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) (syn_wne (syn_cfv H (.cv y)) (.cv x)))
  let syntaxFormula0022 : Wff :=
    (.classMem (syn_cfv H (.cv y))
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
  let syntaxFormula0023 : Wff :=
    (syn_wa (.classMem (syn_cfv H (.cv y)) D) syntaxFormula0022)
  let syntaxFormula0024 : Wff :=
    (syn_wa (.classMem (syn_cfv H (.cv y)) D) syntaxFormula0021)
  let syntaxFormula0025 : Wff :=
    (.classMem (syn_cfv H (syn_cfv H (.cv y)))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  let syntaxFormula0026 : Wff :=
    (syn_wa syntaxFormula0017 (.neg (.classMem (syn_cfv H (.cv y)) (syn_cdm (syn_cin H R)))))
  let syntaxFormula0027 : Wff :=
    (syn_wb (.classMem (.cv y) (syn_cdm (syn_cin H R)))
      (syn_wex w (syn_wbr (.cv y) (syn_cin H R) (.cv w))))
  let syntaxFormula0028 : Wff :=
    (syn_wb (syn_wbr (.cv y) (syn_cin H R) (.cv w))
      (syn_wa (syn_wbr (.cv y) H (.cv w)) (syn_wbr (.cv y) R (.cv w))))
  let syntaxFormula0029 : Wff :=
    (syn_wex w (syn_wa (.classEq (syn_cfv H (.cv y)) (.cv w)) (syn_wbr (.cv y) R (.cv w))))
  let syntaxFormula0030 : Wff :=
    (syn_wex w (syn_wa (.classEq (.cv w) (syn_cfv H (.cv y))) (syn_wbr (.cv y) R (.cv w))))
  let syntaxFormula0031 : Wff := (syn_wb syntaxFormula0029 syntaxFormula0030)
  let syntaxFormula0032 : Wff :=
    (syn_wb syntaxFormula0030 (syn_wbr (.cv y) R (syn_cfv H (.cv y))))
  let syntaxFormula0033 : Wff :=
    (syn_wb (.classMem (.cv y) (syn_cdm (syn_cin H R))) (syn_wbr (.cv y) R (syn_cfv H (.cv y))))
  let syntaxFormula0034 : Wff :=
    (syn_wa syntaxFormula0017
      (.classMem (syn_cfv H (.cv y)) (syn_cdif D (syn_cdm (syn_cin H R)))))
  let syntaxFormula0035 : Wff :=
    (syn_wa syntaxFormula0017 (.classEq (syn_cfv H (.cv y)) (.cv y)))
  let syntaxFormula0036 : Wff :=
    (syn_wa (.classEq (syn_cfv H (syn_cfv H (.cv y))) (.cv w))
      (syn_wbr (syn_cfv H (.cv y)) R (.cv w)))
  let syntaxFormula0037 : Wff :=
    (syn_wa (.classEq (.cv w) (syn_cfv H (syn_cfv H (.cv y))))
      (syn_wbr (syn_cfv H (.cv y)) R (.cv w)))
  let syntaxFormula0038 : Wff := (syn_wex w syntaxFormula0037)
  let syntaxFormula0039 : Wff :=
    (syn_wbr (syn_cfv H (syn_cfv H (.cv y))) syntaxClass0002 (syn_cfv H (.cv y)))
  let syntaxFormula0040 : Wff :=
    (syn_wf1 H D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  let syntaxFormula0041 : Wff := (.neg syntaxFormula0003)
  have p0000 := @g_simpl syntaxFormula0000 syntaxFormula0003
  have p0001 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D))
      (.classMem H (syn_cvv))
  have p0002 :=
    @g_syl syntaxFormula0004 syntaxFormula0000
      (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)) p0000 p0001
  have p0003 := @g_simpl (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)
  have p0004 :=
    @g_syl syntaxFormula0004 (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D))
      (syn_wbr R (syn_cwe) D) p0002 p0003
  have p0005 := (Nominal.classEqRefl (syn_cwe))
  have p0006 := @g_breqi R D (syn_cwe) (syn_cin (syn_cstrict) (syn_cfound)) p0005
  have p0007 := @g_brin R D (syn_cstrict) (syn_cfound)
  have p0008 :=
    @g_bitri (syn_wbr R (syn_cwe) D) (syn_wbr R (syn_cin (syn_cstrict) (syn_cfound)) D)
      (syn_wa (syn_wbr R (syn_cstrict) D) (syn_wbr R (syn_cfound) D)) p0006 p0007
  have p0009 :=
    @g_biimpi (syn_wbr R (syn_cwe) D)
      (syn_wa (syn_wbr R (syn_cstrict) D) (syn_wbr R (syn_cfound) D)) p0008
  have p0010 :=
    @g_syl syntaxFormula0004 (syn_wbr R (syn_cwe) D)
      (syn_wa (syn_wbr R (syn_cstrict) D) (syn_wbr R (syn_cfound) D)) p0004 p0009
  have p0011 :=
    @g_simprd syntaxFormula0004 (syn_wbr R (syn_cstrict) D) (syn_wbr R (syn_cfound) D)
      p0010
  have p0017 := @g_brex R D (syn_cwe)
  have p0018 :=
    @g_syl syntaxFormula0004 (syn_wbr R (syn_cwe) D)
      (syn_wa (.classMem R (syn_cvv)) (.classMem D (syn_cvv))) p0004 p0017
  have p0019 :=
    @g_simprd syntaxFormula0004 (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0018
  have p0021 :=
    @g_simpr (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D))
      (.classMem H (syn_cvv))
  have p0022 :=
    @g_syl syntaxFormula0004 syntaxFormula0000 (.classMem H (syn_cvv)) p0000 p0021
  have p0030 :=
    @g_simpld syntaxFormula0004 (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0018
  have p0031 :=
    @g_jca syntaxFormula0004 (.classMem H (syn_cvv)) (.classMem R (syn_cvv)) p0022 p0030
  have p0032 := @g_inexg H R (syn_cvv) (syn_cvv)
  have p0033 :=
    @g_syl syntaxFormula0004 (syn_wa (.classMem H (syn_cvv)) (.classMem R (syn_cvv)))
      (.classMem (syn_cin H R) (syn_cvv)) p0031 p0032
  have p0034 := @g_dmexg (syn_cin H R) (syn_cvv)
  have p0035 :=
    @g_syl syntaxFormula0004 (.classMem (syn_cin H R) (syn_cvv))
      (.classMem (syn_cdm (syn_cin H R)) (syn_cvv)) p0033 p0034
  have p0036 :=
    @g_jca syntaxFormula0004 (.classMem D (syn_cvv))
      (.classMem (syn_cdm (syn_cin H R)) (syn_cvv)) p0019 p0035
  have p0037 := @g_difexg D (syn_cdm (syn_cin H R)) (syn_cvv) (syn_cvv)
  have p0038 :=
    @g_syl syntaxFormula0004
      (syn_wa (.classMem D (syn_cvv)) (.classMem (syn_cdm (syn_cin H R)) (syn_cvv)))
      (.classMem (syn_cdif D (syn_cdm (syn_cin H R))) (syn_cvv)) p0036 p0037
  have p0039 := @g_difss D (syn_cdm (syn_cin H R))
  have p0040 :=
    @g_a1i (syn_wss (syn_cdif D (syn_cdm (syn_cin H R))) D) syntaxFormula0004 p0039
  have p0044 := @g_simpr (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D)
  have p0045 :=
    @g_syl syntaxFormula0004 (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv x) D))
      (.classMem (.cv x) D) p0002 p0044
  have p0046 := @g_simpl syntaxFormula0004 (syn_wbr (.cv x) R (syn_cfv H (.cv x)))
  have p0058 :=
    @g_simpld syntaxFormula0004 (syn_wbr R (syn_cstrict) D) (syn_wbr R (syn_cfound) D)
      p0010
  have p0059 := @g_sopc D R
  have p0060 :=
    @g_sylib syntaxFormula0004 (syn_wbr R (syn_cstrict) D)
      (syn_wa (syn_wbr R (syn_cpartial) D) (syn_wbr R (syn_cconnex) D)) p0058 p0059
  have p0061 :=
    @g_simpld syntaxFormula0004 (syn_wbr R (syn_cpartial) D) (syn_wbr R (syn_cconnex) D)
      p0060
  have p0062 := @g_porta D R
  have p0063 :=
    @g_sylib syntaxFormula0004 (syn_wbr R (syn_cpartial) D)
      (syn_w3a (syn_wbr R (syn_cref) D) (syn_wbr R (syn_ctrans) D) (syn_wbr R (syn_cantisym) D))
      p0061 p0062
  have p0064 :=
    @g_simp3d syntaxFormula0004 (syn_wbr R (syn_cref) D) (syn_wbr R (syn_ctrans) D)
      (syn_wbr R (syn_cantisym) D) p0063
  have p0065 :=
    @g_syl syntaxFormula0005 syntaxFormula0004 (syn_wbr R (syn_cantisym) D) p0046 p0064
  have p0072 :=
    @g_syl syntaxFormula0005 syntaxFormula0004 (.classMem (.cv x) D) p0046 p0045
  have p0074 := @g_simpr syntaxFormula0000 syntaxFormula0003
  have p0075 :=
    @g_isof1o D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      R syntaxClass0002 H
  have p0076 := @g_syl syntaxFormula0004 syntaxFormula0003 syntaxFormula0006 p0074 p0075
  have p0077 :=
    @g_f1of D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) H
  have p0078 := @g_syl syntaxFormula0004 syntaxFormula0006 syntaxFormula0007 p0076 p0077
  have p0084 :=
    @g_jca syntaxFormula0004 syntaxFormula0007 (.classMem (.cv x) D) p0078 p0045
  have p0085 :=
    @g_ffvelrn D
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (.cv x) H
  have p0086 := @g_syl syntaxFormula0004 syntaxFormula0008 syntaxFormula0009 p0084 p0085
  have p0087 :=
    @g_elin (syn_cfv H (.cv x)) D
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))
  have p0088 := @g_eliniseg (syn_cdif R (syn_cid)) (.cv x) (syn_cfv H (.cv x))
  have p0089 := @g_brdif (syn_cfv H (.cv x)) (.cv x) R (syn_cid)
  have p0090 := @g_vex x
  have p0091 := @g_ideq (syn_cfv H (.cv x)) (.cv x) p0090
  have p0092 :=
    @g_notbii (syn_wbr (syn_cfv H (.cv x)) (syn_cid) (.cv x))
      (.classEq (syn_cfv H (.cv x)) (.cv x)) p0091
  have p0093 := (Nominal.biimpRefl (syn_wne (syn_cfv H (.cv x)) (.cv x)))
  have p0094 :=
    @g_bitr4i (.neg (syn_wbr (syn_cfv H (.cv x)) (syn_cid) (.cv x)))
      (.neg (.classEq (syn_cfv H (.cv x)) (.cv x))) (syn_wne (syn_cfv H (.cv x)) (.cv x))
      p0092 p0093
  have p0095 :=
    @g_anbi2i (.neg (syn_wbr (syn_cfv H (.cv x)) (syn_cid) (.cv x)))
      (syn_wne (syn_cfv H (.cv x)) (.cv x)) (syn_wbr (syn_cfv H (.cv x)) R (.cv x)) p0094
  have p0096 :=
    @g_bitri (syn_wbr (syn_cfv H (.cv x)) (syn_cdif R (syn_cid)) (.cv x))
      syntaxFormula0010 syntaxFormula0011 p0089 p0095
  have p0097 :=
    @g_bitri syntaxFormula0012
      (syn_wbr (syn_cfv H (.cv x)) (syn_cdif R (syn_cid)) (.cv x)) syntaxFormula0011 p0088
      p0096
  have p0098 :=
    @g_anbi2i syntaxFormula0012 syntaxFormula0011 (.classMem (syn_cfv H (.cv x)) D) p0097
  have p0099 := @g_bitri syntaxFormula0009 syntaxFormula0013 syntaxFormula0014 p0087 p0098
  have p0100 := @g_biimpi syntaxFormula0009 syntaxFormula0014 p0099
  have p0101 := @g_syl syntaxFormula0004 syntaxFormula0009 syntaxFormula0014 p0086 p0100
  have p0102 :=
    @g_simpld syntaxFormula0004 (.classMem (syn_cfv H (.cv x)) D) syntaxFormula0011 p0101
  have p0103 :=
    @g_syl syntaxFormula0005 syntaxFormula0004 (.classMem (syn_cfv H (.cv x)) D) p0046
      p0102
  have p0104 := @g_simpr syntaxFormula0004 (syn_wbr (.cv x) R (syn_cfv H (.cv x)))
  have p0134 :=
    @g_simprd syntaxFormula0004 (.classMem (syn_cfv H (.cv x)) D) syntaxFormula0011 p0101
  have p0135 :=
    @g_simpld syntaxFormula0004 (syn_wbr (syn_cfv H (.cv x)) R (.cv x))
      (syn_wne (syn_cfv H (.cv x)) (.cv x)) p0134
  have p0136 :=
    @g_syl syntaxFormula0005 syntaxFormula0004 (syn_wbr (syn_cfv H (.cv x)) R (.cv x))
      p0046 p0135
  have p0137 :=
    @g_antid syntaxFormula0005 D R (.cv x) (syn_cfv H (.cv x)) p0065 p0072 p0103 p0104
      p0136
  have p0138 := @g_eqcomd syntaxFormula0005 (.cv x) (syn_cfv H (.cv x)) p0137
  have p0169 :=
    @g_simprd syntaxFormula0004 (syn_wbr (syn_cfv H (.cv x)) R (.cv x))
      (syn_wne (syn_cfv H (.cv x)) (.cv x)) p0134
  have p0170 :=
    @g_syl syntaxFormula0005 syntaxFormula0004 (syn_wne (syn_cfv H (.cv x)) (.cv x)) p0046
      p0169
  have p0171 :=
    @g_pm2_21ddne syntaxFormula0005 (.neg (syn_wbr (.cv x) R (syn_cfv H (.cv x))))
      (syn_cfv H (.cv x)) (.cv x) p0138 p0170
  have p0172 :=
    @g_pm2_01da syntaxFormula0004 (syn_wbr (.cv x) R (syn_cfv H (.cv x))) p0171
  have p0176 :=
    @g_f1ofn D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      H
  have p0177 := @g_syl syntaxFormula0004 syntaxFormula0006 (syn_wfn H D) p0076 p0176
  have p0183 := @g_jca syntaxFormula0004 (syn_wfn H D) (.classMem (.cv x) D) p0177 p0045
  have p0184 := @g_eldm w (.cv x) (syn_cin H R) dv_cache_0001 dv_cache_0002
  have p0185 :=
    @g_a1i
      (syn_wb (.classMem (.cv x) (syn_cdm (syn_cin H R)))
        (syn_wex w (syn_wbr (.cv x) (syn_cin H R) (.cv w))))
      (syn_wa (syn_wfn H D) (.classMem (.cv x) D)) p0184
  have p0186 := @g_brin (.cv x) (.cv w) H R
  have p0187 :=
    @g_a1i
      (syn_wb (syn_wbr (.cv x) (syn_cin H R) (.cv w))
        (syn_wa (syn_wbr (.cv x) H (.cv w)) (syn_wbr (.cv x) R (.cv w))))
      (syn_wa (syn_wfn H D) (.classMem (.cv x) D)) p0186
  have p0188 := @g_fnbrfvb D (.cv x) (.cv w) H
  have p0189 :=
    @g_bicomd (syn_wa (syn_wfn H D) (.classMem (.cv x) D))
      (.classEq (syn_cfv H (.cv x)) (.cv w)) (syn_wbr (.cv x) H (.cv w)) p0188
  have p0190 :=
    @g_anbi1d (syn_wa (syn_wfn H D) (.classMem (.cv x) D)) (syn_wbr (.cv x) H (.cv w))
      (.classEq (syn_cfv H (.cv x)) (.cv w)) (syn_wbr (.cv x) R (.cv w)) p0189
  have p0191 :=
    @g_bitrd (syn_wa (syn_wfn H D) (.classMem (.cv x) D))
      (syn_wbr (.cv x) (syn_cin H R) (.cv w))
      (syn_wa (syn_wbr (.cv x) H (.cv w)) (syn_wbr (.cv x) R (.cv w)))
      (syn_wa (.classEq (syn_cfv H (.cv x)) (.cv w)) (syn_wbr (.cv x) R (.cv w))) p0187
      p0190
  have p0192 :=
    @g_exbidv (syn_wa (syn_wfn H D) (.classMem (.cv x) D))
      (syn_wbr (.cv x) (syn_cin H R) (.cv w))
      (syn_wa (.classEq (syn_cfv H (.cv x)) (.cv w)) (syn_wbr (.cv x) R (.cv w))) w
      dv_cache_0003 p0191
  have p0193 := @g_eqcom (syn_cfv H (.cv x)) (.cv w)
  have p0194 :=
    @g_anbi1i (.classEq (syn_cfv H (.cv x)) (.cv w))
      (.classEq (.cv w) (syn_cfv H (.cv x))) (syn_wbr (.cv x) R (.cv w)) p0193
  have p0195 :=
    @g_exbii (syn_wa (.classEq (syn_cfv H (.cv x)) (.cv w)) (syn_wbr (.cv x) R (.cv w)))
      (syn_wa (.classEq (.cv w) (syn_cfv H (.cv x))) (syn_wbr (.cv x) R (.cv w))) w p0194
  have p0196 :=
    @g_a1i
      (syn_wb (syn_wex w
          (syn_wa (.classEq (syn_cfv H (.cv x)) (.cv w)) (syn_wbr (.cv x) R (.cv w))))
        syntaxFormula0015)
      (syn_wa (syn_wfn H D) (.classMem (.cv x) D)) p0195
  have p0197 :=
    @g_bitrd (syn_wa (syn_wfn H D) (.classMem (.cv x) D))
      (syn_wex w (syn_wbr (.cv x) (syn_cin H R) (.cv w)))
      (syn_wex w (syn_wa (.classEq (syn_cfv H (.cv x)) (.cv w)) (syn_wbr (.cv x) R (.cv w))))
      syntaxFormula0015 p0192 p0196
  have p0198 := @g_fvex (.cv x) H
  have p0199 := @g_breq2 (.cv w) (syn_cfv H (.cv x)) (.cv x) R
  have p0200 :=
    @g_ceqsexv (syn_wbr (.cv x) R (.cv w)) (syn_wbr (.cv x) R (syn_cfv H (.cv x))) w
      (syn_cfv H (.cv x)) dv_cache_0004 dv_cache_0005 p0198 p0199
  have p0201 :=
    @g_a1i (syn_wb syntaxFormula0015 (syn_wbr (.cv x) R (syn_cfv H (.cv x))))
      (syn_wa (syn_wfn H D) (.classMem (.cv x) D)) p0200
  have p0202 :=
    @g_bitrd (syn_wa (syn_wfn H D) (.classMem (.cv x) D))
      (syn_wex w (syn_wbr (.cv x) (syn_cin H R) (.cv w))) syntaxFormula0015
      (syn_wbr (.cv x) R (syn_cfv H (.cv x))) p0197 p0201
  have p0203 :=
    @g_bitrd (syn_wa (syn_wfn H D) (.classMem (.cv x) D))
      (.classMem (.cv x) (syn_cdm (syn_cin H R)))
      (syn_wex w (syn_wbr (.cv x) (syn_cin H R) (.cv w)))
      (syn_wbr (.cv x) R (syn_cfv H (.cv x))) p0185 p0202
  have p0204 :=
    @g_syl syntaxFormula0004 (syn_wa (syn_wfn H D) (.classMem (.cv x) D))
      (syn_wb (.classMem (.cv x) (syn_cdm (syn_cin H R)))
        (syn_wbr (.cv x) R (syn_cfv H (.cv x))))
      p0183 p0203
  have p0205 :=
    @g_biimpd syntaxFormula0004 (.classMem (.cv x) (syn_cdm (syn_cin H R)))
      (syn_wbr (.cv x) R (syn_cfv H (.cv x))) p0204
  have p0206 :=
    @g_mtod syntaxFormula0004 (.classMem (.cv x) (syn_cdm (syn_cin H R)))
      (syn_wbr (.cv x) R (syn_cfv H (.cv x))) p0172 p0205
  have p0207 :=
    @g_jca syntaxFormula0004 (.classMem (.cv x) D)
      (.neg (.classMem (.cv x) (syn_cdm (syn_cin H R)))) p0045 p0206
  have p0208 := @g_eldif (.cv x) D (syn_cdm (syn_cin H R))
  have p0209 :=
    @g_biimpri (.classMem (.cv x) (syn_cdif D (syn_cdm (syn_cin H R))))
      (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) (syn_cdm (syn_cin H R)))))
      p0208
  have p0210 :=
    @g_syl syntaxFormula0004
      (syn_wa (.classMem (.cv x) D) (.neg (.classMem (.cv x) (syn_cdm (syn_cin H R)))))
      (.classMem (.cv x) (syn_cdif D (syn_cdm (syn_cin H R)))) p0207 p0209
  have p0211 := @g_ne0i (syn_cdif D (syn_cdm (syn_cin H R))) (.cv x)
  have p0212 :=
    @g_syl syntaxFormula0004 (.classMem (.cv x) (syn_cdif D (syn_cdm (syn_cin H R))))
      (syn_wne (syn_cdif D (syn_cdm (syn_cin H R))) (syn_c0)) p0210 p0211
  have p0213 :=
    @g_frd syntaxFormula0004 y z D R (syn_cvv) (syn_cdif D (syn_cdm (syn_cin H R)))
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 p0011 p0038
      p0040 p0212
  have p0214 :=
    @g_simp1 syntaxFormula0004 (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R))))
      syntaxFormula0016
  have p0233 :=
    @g_syl syntaxFormula0017 syntaxFormula0004 (syn_wbr R (syn_cantisym) D) p0214 p0064
  have p0240 := @g_syl syntaxFormula0017 syntaxFormula0004 syntaxFormula0007 p0214 p0078
  have p0241 :=
    @g_simp2 syntaxFormula0004 (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R))))
      syntaxFormula0016
  have p0242 := @g_eldifi (.cv y) D (syn_cdm (syn_cin H R))
  have p0243 :=
    @g_syl syntaxFormula0017 (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R))))
      (.classMem (.cv y) D) p0241 p0242
  have p0244 :=
    @g_jca syntaxFormula0017 syntaxFormula0007 (.classMem (.cv y) D) p0240 p0243
  have p0245 :=
    @g_ffvelrn D
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (.cv y) H
  have p0246 := @g_syl syntaxFormula0017 syntaxFormula0018 syntaxFormula0019 p0244 p0245
  have p0247 :=
    @g_elin (syn_cfv H (.cv y)) D
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))
  have p0248 := @g_eliniseg (syn_cdif R (syn_cid)) (.cv x) (syn_cfv H (.cv y))
  have p0249 := @g_brdif (syn_cfv H (.cv y)) (.cv x) R (syn_cid)
  have p0251 := @g_ideq (syn_cfv H (.cv y)) (.cv x) p0090
  have p0252 :=
    @g_notbii (syn_wbr (syn_cfv H (.cv y)) (syn_cid) (.cv x))
      (.classEq (syn_cfv H (.cv y)) (.cv x)) p0251
  have p0253 := (Nominal.biimpRefl (syn_wne (syn_cfv H (.cv y)) (.cv x)))
  have p0254 :=
    @g_bitr4i (.neg (syn_wbr (syn_cfv H (.cv y)) (syn_cid) (.cv x)))
      (.neg (.classEq (syn_cfv H (.cv y)) (.cv x))) (syn_wne (syn_cfv H (.cv y)) (.cv x))
      p0252 p0253
  have p0255 :=
    @g_anbi2i (.neg (syn_wbr (syn_cfv H (.cv y)) (syn_cid) (.cv x)))
      (syn_wne (syn_cfv H (.cv y)) (.cv x)) (syn_wbr (syn_cfv H (.cv y)) R (.cv x)) p0254
  have p0256 :=
    @g_bitri (syn_wbr (syn_cfv H (.cv y)) (syn_cdif R (syn_cid)) (.cv x))
      syntaxFormula0020 syntaxFormula0021 p0249 p0255
  have p0257 :=
    @g_bitri syntaxFormula0022
      (syn_wbr (syn_cfv H (.cv y)) (syn_cdif R (syn_cid)) (.cv x)) syntaxFormula0021 p0248
      p0256
  have p0258 :=
    @g_anbi2i syntaxFormula0022 syntaxFormula0021 (.classMem (syn_cfv H (.cv y)) D) p0257
  have p0259 := @g_bitri syntaxFormula0019 syntaxFormula0023 syntaxFormula0024 p0247 p0258
  have p0260 := @g_biimpi syntaxFormula0019 syntaxFormula0024 p0259
  have p0261 := @g_syl syntaxFormula0017 syntaxFormula0019 syntaxFormula0024 p0246 p0260
  have p0262 :=
    @g_simpld syntaxFormula0017 (.classMem (syn_cfv H (.cv y)) D) syntaxFormula0021 p0261
  have p0299 :=
    @g_jca syntaxFormula0017 syntaxFormula0007 (.classMem (syn_cfv H (.cv y)) D) p0240
      p0262
  have p0300 :=
    @g_ffvelrn D
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cfv H (.cv y)) H
  have p0301 :=
    @g_syl syntaxFormula0017 (syn_wa syntaxFormula0007 (.classMem (syn_cfv H (.cv y)) D))
      syntaxFormula0025 p0299 p0300
  have p0302 := @g_inss1 D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))
  have p0303 :=
    @g_sseli (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) D
      (syn_cfv H (syn_cfv H (.cv y))) p0302
  have p0304 :=
    @g_syl syntaxFormula0017 syntaxFormula0025
      (.classMem (syn_cfv H (syn_cfv H (.cv y))) D) p0301 p0303
  have p0305 := @g_id (.classMem (syn_cfv H (.cv y)) (syn_cdm (syn_cin H R)))
  have p0306 :=
    @g_a1i
      (.imp (.classMem (syn_cfv H (.cv y)) (syn_cdm (syn_cin H R)))
        (.classMem (syn_cfv H (.cv y)) (syn_cdm (syn_cin H R))))
      syntaxFormula0017 p0305
  have p0307 :=
    @g_simpl syntaxFormula0017
      (.neg (.classMem (syn_cfv H (.cv y)) (syn_cdm (syn_cin H R))))
  have p0337 :=
    @g_syl syntaxFormula0026 syntaxFormula0017 (.classMem (syn_cfv H (.cv y)) D) p0307
      p0262
  have p0338 :=
    @g_simpr syntaxFormula0017
      (.neg (.classMem (syn_cfv H (.cv y)) (syn_cdm (syn_cin H R))))
  have p0339 :=
    @g_jca syntaxFormula0026 (.classMem (syn_cfv H (.cv y)) D)
      (.neg (.classMem (syn_cfv H (.cv y)) (syn_cdm (syn_cin H R)))) p0337 p0338
  have p0340 := @g_eldif (syn_cfv H (.cv y)) D (syn_cdm (syn_cin H R))
  have p0341 :=
    @g_biimpri (.classMem (syn_cfv H (.cv y)) (syn_cdif D (syn_cdm (syn_cin H R))))
      (syn_wa (.classMem (syn_cfv H (.cv y)) D)
        (.neg (.classMem (syn_cfv H (.cv y)) (syn_cdm (syn_cin H R)))))
      p0340
  have p0342 :=
    @g_syl syntaxFormula0026
      (syn_wa (.classMem (syn_cfv H (.cv y)) D)
        (.neg (.classMem (syn_cfv H (.cv y)) (syn_cdm (syn_cin H R)))))
      (.classMem (syn_cfv H (.cv y)) (syn_cdif D (syn_cdm (syn_cin H R)))) p0339 p0341
  have p0344 :=
    @g_simpl syntaxFormula0017
      (.classMem (syn_cfv H (.cv y)) (syn_cdif D (syn_cdm (syn_cin H R))))
  have p0346 := @g_eldifn (.cv y) D (syn_cdm (syn_cin H R))
  have p0347 :=
    @g_syl syntaxFormula0017 (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R))))
      (.neg (.classMem (.cv y) (syn_cdm (syn_cin H R)))) p0241 p0346
  have p0354 := @g_syl syntaxFormula0017 syntaxFormula0004 (syn_wfn H D) p0214 p0177
  have p0358 := @g_jca syntaxFormula0017 (syn_wfn H D) (.classMem (.cv y) D) p0354 p0243
  have p0359 := @g_eldm w (.cv y) (syn_cin H R) dv_cache_0011 dv_cache_0002
  have p0360 :=
    @g_a1i syntaxFormula0027 (syn_wa (syn_wfn H D) (.classMem (.cv y) D)) p0359
  have p0361 := @g_brin (.cv y) (.cv w) H R
  have p0362 :=
    @g_a1i syntaxFormula0028 (syn_wa (syn_wfn H D) (.classMem (.cv y) D)) p0361
  have p0363 := @g_fnbrfvb D (.cv y) (.cv w) H
  have p0364 :=
    @g_bicomd (syn_wa (syn_wfn H D) (.classMem (.cv y) D))
      (.classEq (syn_cfv H (.cv y)) (.cv w)) (syn_wbr (.cv y) H (.cv w)) p0363
  have p0365 :=
    @g_anbi1d (syn_wa (syn_wfn H D) (.classMem (.cv y) D)) (syn_wbr (.cv y) H (.cv w))
      (.classEq (syn_cfv H (.cv y)) (.cv w)) (syn_wbr (.cv y) R (.cv w)) p0364
  have p0366 :=
    @g_bitrd (syn_wa (syn_wfn H D) (.classMem (.cv y) D))
      (syn_wbr (.cv y) (syn_cin H R) (.cv w))
      (syn_wa (syn_wbr (.cv y) H (.cv w)) (syn_wbr (.cv y) R (.cv w)))
      (syn_wa (.classEq (syn_cfv H (.cv y)) (.cv w)) (syn_wbr (.cv y) R (.cv w))) p0362
      p0365
  have p0367 :=
    @g_exbidv (syn_wa (syn_wfn H D) (.classMem (.cv y) D))
      (syn_wbr (.cv y) (syn_cin H R) (.cv w))
      (syn_wa (.classEq (syn_cfv H (.cv y)) (.cv w)) (syn_wbr (.cv y) R (.cv w))) w
      dv_cache_0012 p0366
  have p0368 := @g_eqcom (syn_cfv H (.cv y)) (.cv w)
  have p0369 :=
    @g_anbi1i (.classEq (syn_cfv H (.cv y)) (.cv w))
      (.classEq (.cv w) (syn_cfv H (.cv y))) (syn_wbr (.cv y) R (.cv w)) p0368
  have p0370 :=
    @g_exbii (syn_wa (.classEq (syn_cfv H (.cv y)) (.cv w)) (syn_wbr (.cv y) R (.cv w)))
      (syn_wa (.classEq (.cv w) (syn_cfv H (.cv y))) (syn_wbr (.cv y) R (.cv w))) w p0369
  have p0371 :=
    @g_a1i syntaxFormula0031 (syn_wa (syn_wfn H D) (.classMem (.cv y) D)) p0370
  have p0372 :=
    @g_bitrd (syn_wa (syn_wfn H D) (.classMem (.cv y) D))
      (syn_wex w (syn_wbr (.cv y) (syn_cin H R) (.cv w))) syntaxFormula0029
      syntaxFormula0030 p0367 p0371
  have p0373 := @g_fvex (.cv y) H
  have p0374 := @g_breq2 (.cv w) (syn_cfv H (.cv y)) (.cv y) R
  have p0375 :=
    @g_ceqsexv (syn_wbr (.cv y) R (.cv w)) (syn_wbr (.cv y) R (syn_cfv H (.cv y))) w
      (syn_cfv H (.cv y)) dv_cache_0013 dv_cache_0014 p0373 p0374
  have p0376 :=
    @g_a1i syntaxFormula0032 (syn_wa (syn_wfn H D) (.classMem (.cv y) D)) p0375
  have p0377 :=
    @g_bitrd (syn_wa (syn_wfn H D) (.classMem (.cv y) D))
      (syn_wex w (syn_wbr (.cv y) (syn_cin H R) (.cv w))) syntaxFormula0030
      (syn_wbr (.cv y) R (syn_cfv H (.cv y))) p0372 p0376
  have p0378 :=
    @g_bitrd (syn_wa (syn_wfn H D) (.classMem (.cv y) D))
      (.classMem (.cv y) (syn_cdm (syn_cin H R)))
      (syn_wex w (syn_wbr (.cv y) (syn_cin H R) (.cv w)))
      (syn_wbr (.cv y) R (syn_cfv H (.cv y))) p0360 p0377
  have p0379 :=
    @g_syl syntaxFormula0017 (syn_wa (syn_wfn H D) (.classMem (.cv y) D))
      syntaxFormula0033 p0358 p0378
  have p0380 :=
    @g_biimprd syntaxFormula0017 (.classMem (.cv y) (syn_cdm (syn_cin H R)))
      (syn_wbr (.cv y) R (syn_cfv H (.cv y))) p0379
  have p0381 :=
    @g_mtod syntaxFormula0017 (syn_wbr (.cv y) R (syn_cfv H (.cv y)))
      (.classMem (.cv y) (syn_cdm (syn_cin H R))) p0347 p0380
  have p0397 :=
    @g_simprd syntaxFormula0004 (syn_wbr R (syn_cpartial) D) (syn_wbr R (syn_cconnex) D)
      p0060
  have p0398 :=
    @g_syl syntaxFormula0017 syntaxFormula0004 (syn_wbr R (syn_cconnex) D) p0214 p0397
  have p0431 :=
    @g_connexd syntaxFormula0017 D R (.cv y) (syn_cfv H (.cv y)) p0398 p0243 p0262
  have p0432 :=
    @g_ord syntaxFormula0017 (syn_wbr (.cv y) R (syn_cfv H (.cv y)))
      (syn_wbr (syn_cfv H (.cv y)) R (.cv y)) p0431
  have p0433 :=
    @g_mpd syntaxFormula0017 (.neg (syn_wbr (.cv y) R (syn_cfv H (.cv y))))
      (syn_wbr (syn_cfv H (.cv y)) R (.cv y)) p0381 p0432
  have p0434 :=
    @g_syl syntaxFormula0034 syntaxFormula0017 (syn_wbr (syn_cfv H (.cv y)) R (.cv y))
      p0344 p0433
  have p0436 :=
    @g_simp3 syntaxFormula0004 (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R))))
      syntaxFormula0016
  have p0437 := @g_syl syntaxFormula0034 syntaxFormula0017 syntaxFormula0016 p0344 p0436
  have p0438 :=
    @g_simpr syntaxFormula0017
      (.classMem (syn_cfv H (.cv y)) (syn_cdif D (syn_cdm (syn_cin H R))))
  have p0439 :=
    @g_jca syntaxFormula0034 syntaxFormula0016
      (.classMem (syn_cfv H (.cv y)) (syn_cdif D (syn_cdm (syn_cin H R)))) p0437 p0438
  have p0440 := @g_breq1 (.cv z) (syn_cfv H (.cv y)) (.cv y) R
  have p0441 := @g_eqeq1 (.cv z) (syn_cfv H (.cv y)) (.cv y)
  have p0442 :=
    @g_imbi12d (.classEq (.cv z) (syn_cfv H (.cv y))) (syn_wbr (.cv z) R (.cv y))
      (syn_wbr (syn_cfv H (.cv y)) R (.cv y)) (.classEq (.cv z) (.cv y))
      (.classEq (syn_cfv H (.cv y)) (.cv y)) p0440 p0441
  have p0443 :=
    @g_rspccva (.imp (syn_wbr (.cv z) R (.cv y)) (.classEq (.cv z) (.cv y)))
      (.imp (syn_wbr (syn_cfv H (.cv y)) R (.cv y)) (.classEq (syn_cfv H (.cv y)) (.cv y)))
      z (syn_cfv H (.cv y)) (syn_cdif D (syn_cdm (syn_cin H R))) dv_cache_0015
      dv_cache_0009 dv_cache_0016 p0442
  have p0444 :=
    @g_syl syntaxFormula0034
      (syn_wa syntaxFormula0016
        (.classMem (syn_cfv H (.cv y)) (syn_cdif D (syn_cdm (syn_cin H R)))))
      (.imp (syn_wbr (syn_cfv H (.cv y)) R (.cv y)) (.classEq (syn_cfv H (.cv y)) (.cv y)))
      p0439 p0443
  have p0445 :=
    @g_mpd syntaxFormula0034 (syn_wbr (syn_cfv H (.cv y)) R (.cv y))
      (.classEq (syn_cfv H (.cv y)) (.cv y)) p0434 p0444
  have p0447 := @g_simpr syntaxFormula0017 (.classEq (syn_cfv H (.cv y)) (.cv y))
  have p0448 := @g_simpl syntaxFormula0017 (.classEq (syn_cfv H (.cv y)) (.cv y))
  have p0538 :=
    @g_syl syntaxFormula0035 syntaxFormula0017 (syn_wbr (syn_cfv H (.cv y)) R (.cv y))
      p0448 p0433
  have p0539 :=
    @g_eqbrtrrd syntaxFormula0035 (syn_cfv H (.cv y)) (.cv y) (.cv y) R p0447 p0538
  have p0541 :=
    @g_breqtrrd syntaxFormula0035 (.cv y) (.cv y) (syn_cfv H (.cv y)) R p0539 p0447
  have p0580 :=
    @g_syl syntaxFormula0035 syntaxFormula0017
      (.neg (syn_wbr (.cv y) R (syn_cfv H (.cv y)))) p0448 p0381
  have p0581 :=
    @g_pm2_21dd syntaxFormula0035 (syn_wbr (.cv y) R (syn_cfv H (.cv y)))
      (.neg (.classEq (syn_cfv H (.cv y)) (.cv y))) p0541 p0580
  have p0582 := @g_pm2_01da syntaxFormula0017 (.classEq (syn_cfv H (.cv y)) (.cv y)) p0581
  have p0583 := (Nominal.biimpRefl (syn_wne (syn_cfv H (.cv y)) (.cv y)))
  have p0584 :=
    @g_biimpri (syn_wne (syn_cfv H (.cv y)) (.cv y))
      (.neg (.classEq (syn_cfv H (.cv y)) (.cv y))) p0583
  have p0585 :=
    @g_syl syntaxFormula0017 (.neg (.classEq (syn_cfv H (.cv y)) (.cv y)))
      (syn_wne (syn_cfv H (.cv y)) (.cv y)) p0582 p0584
  have p0586 :=
    @g_syl syntaxFormula0034 syntaxFormula0017 (syn_wne (syn_cfv H (.cv y)) (.cv y)) p0344
      p0585
  have p0587 :=
    @g_pm2_21ddne syntaxFormula0034
      (.neg (.classMem (syn_cfv H (.cv y)) (syn_cdif D (syn_cdm (syn_cin H R)))))
      (syn_cfv H (.cv y)) (.cv y) p0445 p0586
  have p0588 :=
    @g_pm2_01da syntaxFormula0017
      (.classMem (syn_cfv H (.cv y)) (syn_cdif D (syn_cdm (syn_cin H R)))) p0587
  have p0589 :=
    @g_syl syntaxFormula0026 syntaxFormula0017
      (.neg (.classMem (syn_cfv H (.cv y)) (syn_cdif D (syn_cdm (syn_cin H R))))) p0307
      p0588
  have p0590 :=
    @g_pm2_21dd syntaxFormula0026
      (.classMem (syn_cfv H (.cv y)) (syn_cdif D (syn_cdm (syn_cin H R))))
      (.classMem (syn_cfv H (.cv y)) (syn_cdm (syn_cin H R))) p0342 p0589
  have p0591 :=
    @g_ex syntaxFormula0017 (.neg (.classMem (syn_cfv H (.cv y)) (syn_cdm (syn_cin H R))))
      (.classMem (syn_cfv H (.cv y)) (syn_cdm (syn_cin H R))) p0590
  have p0592 :=
    @g_pm2_61d syntaxFormula0017 (.classMem (syn_cfv H (.cv y)) (syn_cdm (syn_cin H R)))
      (.classMem (syn_cfv H (.cv y)) (syn_cdm (syn_cin H R))) p0306 p0591
  have p0629 :=
    @g_jca syntaxFormula0017 (syn_wfn H D) (.classMem (syn_cfv H (.cv y)) D) p0354 p0262
  have p0630 := @g_eldm w (syn_cfv H (.cv y)) (syn_cin H R) dv_cache_0013 dv_cache_0002
  have p0631 :=
    @g_a1i
      (syn_wb (.classMem (syn_cfv H (.cv y)) (syn_cdm (syn_cin H R)))
        (syn_wex w (syn_wbr (syn_cfv H (.cv y)) (syn_cin H R) (.cv w))))
      (syn_wa (syn_wfn H D) (.classMem (syn_cfv H (.cv y)) D)) p0630
  have p0632 := @g_brin (syn_cfv H (.cv y)) (.cv w) H R
  have p0633 :=
    @g_a1i
      (syn_wb (syn_wbr (syn_cfv H (.cv y)) (syn_cin H R) (.cv w))
        (syn_wa (syn_wbr (syn_cfv H (.cv y)) H (.cv w))
          (syn_wbr (syn_cfv H (.cv y)) R (.cv w))))
      (syn_wa (syn_wfn H D) (.classMem (syn_cfv H (.cv y)) D)) p0632
  have p0634 := @g_fnbrfvb D (syn_cfv H (.cv y)) (.cv w) H
  have p0635 :=
    @g_bicomd (syn_wa (syn_wfn H D) (.classMem (syn_cfv H (.cv y)) D))
      (.classEq (syn_cfv H (syn_cfv H (.cv y))) (.cv w))
      (syn_wbr (syn_cfv H (.cv y)) H (.cv w)) p0634
  have p0636 :=
    @g_anbi1d (syn_wa (syn_wfn H D) (.classMem (syn_cfv H (.cv y)) D))
      (syn_wbr (syn_cfv H (.cv y)) H (.cv w))
      (.classEq (syn_cfv H (syn_cfv H (.cv y))) (.cv w))
      (syn_wbr (syn_cfv H (.cv y)) R (.cv w)) p0635
  have p0637 :=
    @g_bitrd (syn_wa (syn_wfn H D) (.classMem (syn_cfv H (.cv y)) D))
      (syn_wbr (syn_cfv H (.cv y)) (syn_cin H R) (.cv w))
      (syn_wa (syn_wbr (syn_cfv H (.cv y)) H (.cv w)) (syn_wbr (syn_cfv H (.cv y)) R (.cv w)))
      syntaxFormula0036 p0633 p0636
  have p0638 :=
    @g_exbidv (syn_wa (syn_wfn H D) (.classMem (syn_cfv H (.cv y)) D))
      (syn_wbr (syn_cfv H (.cv y)) (syn_cin H R) (.cv w)) syntaxFormula0036 w
      dv_cache_0017 p0637
  have p0639 := @g_eqcom (syn_cfv H (syn_cfv H (.cv y))) (.cv w)
  have p0640 :=
    @g_anbi1i (.classEq (syn_cfv H (syn_cfv H (.cv y))) (.cv w))
      (.classEq (.cv w) (syn_cfv H (syn_cfv H (.cv y))))
      (syn_wbr (syn_cfv H (.cv y)) R (.cv w)) p0639
  have p0641 := @g_exbii syntaxFormula0036 syntaxFormula0037 w p0640
  have p0642 :=
    @g_a1i (syn_wb (syn_wex w syntaxFormula0036) syntaxFormula0038)
      (syn_wa (syn_wfn H D) (.classMem (syn_cfv H (.cv y)) D)) p0641
  have p0643 :=
    @g_bitrd (syn_wa (syn_wfn H D) (.classMem (syn_cfv H (.cv y)) D))
      (syn_wex w (syn_wbr (syn_cfv H (.cv y)) (syn_cin H R) (.cv w)))
      (syn_wex w syntaxFormula0036) syntaxFormula0038 p0638 p0642
  have p0644 := @g_fvex (syn_cfv H (.cv y)) H
  have p0645 := @g_breq2 (.cv w) (syn_cfv H (syn_cfv H (.cv y))) (syn_cfv H (.cv y)) R
  have p0646 :=
    @g_ceqsexv (syn_wbr (syn_cfv H (.cv y)) R (.cv w))
      (syn_wbr (syn_cfv H (.cv y)) R (syn_cfv H (syn_cfv H (.cv y)))) w
      (syn_cfv H (syn_cfv H (.cv y))) dv_cache_0018 dv_cache_0019 p0644 p0645
  have p0647 :=
    @g_a1i
      (syn_wb syntaxFormula0038 (syn_wbr (syn_cfv H (.cv y)) R (syn_cfv H (syn_cfv H (.cv y)))))
      (syn_wa (syn_wfn H D) (.classMem (syn_cfv H (.cv y)) D)) p0646
  have p0648 :=
    @g_bitrd (syn_wa (syn_wfn H D) (.classMem (syn_cfv H (.cv y)) D))
      (syn_wex w (syn_wbr (syn_cfv H (.cv y)) (syn_cin H R) (.cv w))) syntaxFormula0038
      (syn_wbr (syn_cfv H (.cv y)) R (syn_cfv H (syn_cfv H (.cv y)))) p0643 p0647
  have p0649 :=
    @g_bitrd (syn_wa (syn_wfn H D) (.classMem (syn_cfv H (.cv y)) D))
      (.classMem (syn_cfv H (.cv y)) (syn_cdm (syn_cin H R)))
      (syn_wex w (syn_wbr (syn_cfv H (.cv y)) (syn_cin H R) (.cv w)))
      (syn_wbr (syn_cfv H (.cv y)) R (syn_cfv H (syn_cfv H (.cv y)))) p0631 p0648
  have p0650 :=
    @g_syl syntaxFormula0017 (syn_wa (syn_wfn H D) (.classMem (syn_cfv H (.cv y)) D))
      (syn_wb (.classMem (syn_cfv H (.cv y)) (syn_cdm (syn_cin H R)))
        (syn_wbr (syn_cfv H (.cv y)) R (syn_cfv H (syn_cfv H (.cv y)))))
      p0629 p0649
  have p0651 :=
    @g_biimpd syntaxFormula0017 (.classMem (syn_cfv H (.cv y)) (syn_cdm (syn_cin H R)))
      (syn_wbr (syn_cfv H (.cv y)) R (syn_cfv H (syn_cfv H (.cv y)))) p0650
  have p0652 :=
    @g_mpd syntaxFormula0017 (.classMem (syn_cfv H (.cv y)) (syn_cdm (syn_cin H R)))
      (syn_wbr (syn_cfv H (.cv y)) R (syn_cfv H (syn_cfv H (.cv y)))) p0592 p0651
  have p0744 := @g_syl syntaxFormula0017 syntaxFormula0004 syntaxFormula0003 p0214 p0074
  have p0777 :=
    @g_jca syntaxFormula0017 (.classMem (syn_cfv H (.cv y)) D) (.classMem (.cv y) D) p0262
      p0243
  have p0778 :=
    @g_jca syntaxFormula0017 syntaxFormula0003
      (syn_wa (.classMem (syn_cfv H (.cv y)) D) (.classMem (.cv y) D)) p0744 p0777
  have p0779 :=
    @g_isorel D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cfv H (.cv y)) (.cv y) R syntaxClass0002 H
  have p0780 :=
    @g_syl syntaxFormula0017
      (syn_wa syntaxFormula0003
        (syn_wa (.classMem (syn_cfv H (.cv y)) D) (.classMem (.cv y) D)))
      (syn_wb (syn_wbr (syn_cfv H (.cv y)) R (.cv y)) syntaxFormula0039) p0778 p0779
  have p0833 := @g_jca syntaxFormula0017 syntaxFormula0025 syntaxFormula0019 p0301 p0246
  have p0834 :=
    @g_brinxp (syn_cfv H (syn_cfv H (.cv y))) (syn_cfv H (.cv y))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) R
  have p0835 :=
    @g_syl syntaxFormula0017 (syn_wa syntaxFormula0025 syntaxFormula0019)
      (syn_wb (syn_wbr (syn_cfv H (syn_cfv H (.cv y))) R (syn_cfv H (.cv y))) syntaxFormula0039)
      p0833 p0834
  have p0836 :=
    @g_bitr4d syntaxFormula0017 (syn_wbr (syn_cfv H (.cv y)) R (.cv y)) syntaxFormula0039
      (syn_wbr (syn_cfv H (syn_cfv H (.cv y))) R (syn_cfv H (.cv y))) p0780 p0835
  have p0837 :=
    @g_biimpd syntaxFormula0017 (syn_wbr (syn_cfv H (.cv y)) R (.cv y))
      (syn_wbr (syn_cfv H (syn_cfv H (.cv y))) R (syn_cfv H (.cv y))) p0836
  have p0838 :=
    @g_mpd syntaxFormula0017 (syn_wbr (syn_cfv H (.cv y)) R (.cv y))
      (syn_wbr (syn_cfv H (syn_cfv H (.cv y))) R (syn_cfv H (.cv y))) p0433 p0837
  have p0839 :=
    @g_antid syntaxFormula0017 D R (syn_cfv H (.cv y)) (syn_cfv H (syn_cfv H (.cv y)))
      p0233 p0262 p0304 p0652 p0838
  have p0840 :=
    @g_eqcomd syntaxFormula0017 (syn_cfv H (.cv y)) (syn_cfv H (syn_cfv H (.cv y))) p0839
  have p0845 :=
    @g_f1of1 D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      H
  have p0846 := @g_syl syntaxFormula0004 syntaxFormula0006 syntaxFormula0040 p0076 p0845
  have p0847 := @g_syl syntaxFormula0017 syntaxFormula0004 syntaxFormula0040 p0214 p0846
  have p0881 :=
    @g_jca syntaxFormula0017 syntaxFormula0040
      (syn_wa (.classMem (syn_cfv H (.cv y)) D) (.classMem (.cv y) D)) p0847 p0777
  have p0882 :=
    @g_f1fveq D (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cfv H (.cv y)) (.cv y) H
  have p0883 :=
    @g_syl syntaxFormula0017
      (syn_wa syntaxFormula0040
        (syn_wa (.classMem (syn_cfv H (.cv y)) D) (.classMem (.cv y) D)))
      (syn_wb (.classEq (syn_cfv H (syn_cfv H (.cv y))) (syn_cfv H (.cv y)))
        (.classEq (syn_cfv H (.cv y)) (.cv y)))
      p0881 p0882
  have p0884 :=
    @g_biimpd syntaxFormula0017
      (.classEq (syn_cfv H (syn_cfv H (.cv y))) (syn_cfv H (.cv y)))
      (.classEq (syn_cfv H (.cv y)) (.cv y)) p0883
  have p0885 :=
    @g_mpd syntaxFormula0017
      (.classEq (syn_cfv H (syn_cfv H (.cv y))) (syn_cfv H (.cv y)))
      (.classEq (syn_cfv H (.cv y)) (.cv y)) p0840 p0884
  have p1025 :=
    @g_pm2_21ddne syntaxFormula0017 syntaxFormula0041 (syn_cfv H (.cv y)) (.cv y) p0885
      p0585
  have p1026 :=
    @g_n_3exp syntaxFormula0004 (.classMem (.cv y) (syn_cdif D (syn_cdm (syn_cin H R))))
      syntaxFormula0016 syntaxFormula0041 p1025
  have p1027 :=
    @g_rexlimdv syntaxFormula0004 syntaxFormula0016 syntaxFormula0041 y
      (syn_cdif D (syn_cdm (syn_cin H R))) dv_cache_0020 dv_cache_0021 p1026
  have p1028_e00_recanon :
    Nominal.NPrf
      (.imp syntaxFormula0004
        (syn_wrex y (syn_cdif D (syn_cdm (syn_cin H R))) syntaxFormula0016)) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wa, syn_cin, syn_ccompl, syn_cnin, syn_wnan, syn_copab, syn_wex,
          syn_wrex, syn_cdif, syn_cdm, syn_crn, syn_cima, syn_cvv, syn_ccnv, syn_wral,
          syn_wbr, syn_cop, syn_cun]
        simp (config :=
          {
            failIfUnchanged :=
              false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.all
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _)
      p0213
  have p1028 :=
    @g_mpd syntaxFormula0004
      (syn_wrex y (syn_cdif D (syn_cdm (syn_cin H R))) syntaxFormula0016)
      syntaxFormula0041 p1028_e00_recanon p1027
  have p1029 := @g_pm2_01da syntaxFormula0000 syntaxFormula0003 p1028
  exact p1029


end NFChoice.DirectNominalPrf.WPPReplay

end

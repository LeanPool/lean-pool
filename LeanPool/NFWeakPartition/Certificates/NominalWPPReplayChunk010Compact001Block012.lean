/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk010Compact001Block011

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk010Compact001Part034`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_phi011lem1 (A : Class) (B : Class) :
    Nominal.NPrf
      (.imp (.classEq (syn_cun (syn_cphi A) (syn_csn (syn_c0c)))
          (syn_cun (syn_cphi B) (syn_csn (syn_c0c)))) (syn_wss (syn_cphi A) (syn_cphi B))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (h))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have dv_cache_0001 : z ∉ ((syn_c0c)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0002 : z ∉ ((syn_cphi A)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cphi, fresh_z_not_A,
          not_false_eq_true])
  have dv_cache_0003 : z ∉ ((syn_cphi B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cphi, fresh_z_not_B,
          not_false_eq_true])
  have dv_cache_0004 :
    z ∉
      ((Wff.classEq (syn_cun (syn_cphi A) (syn_csn (syn_c0c)))
          (syn_cun (syn_cphi B) (syn_csn (syn_c0c))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cphi,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
          fresh_z_not_A, fresh_z_not_B, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have p0000 := @g_ssun1 (syn_cphi A) (syn_csn (syn_c0c))
  have p0001 :=
    @g_sseli (syn_cphi A) (syn_cun (syn_cphi A) (syn_csn (syn_c0c))) (.cv z) p0000
  have p0002 :=
    @g_eleq2 (syn_cun (syn_cphi A) (syn_csn (syn_c0c)))
      (syn_cun (syn_cphi B) (syn_csn (syn_c0c))) (.cv z)
  have p0003 :=
    @g_syl5ib (.classMem (.cv z) (syn_cphi A))
      (.classMem (.cv z) (syn_cun (syn_cphi A) (syn_csn (syn_c0c))))
      (.classEq (syn_cun (syn_cphi A) (syn_csn (syn_c0c)))
        (syn_cun (syn_cphi B) (syn_csn (syn_c0c))))
      (.classMem (.cv z) (syn_cun (syn_cphi B) (syn_csn (syn_c0c)))) p0001 p0002
  have p0004 := @g_n_0cnelphi A
  have p0005 := @g_eleq1 (.cv z) (syn_c0c) (syn_cphi A)
  have p0006 :=
    @g_mtbiri (.classEq (.cv z) (syn_c0c)) (.classMem (.cv z) (syn_cphi A))
      (.classMem (syn_c0c) (syn_cphi A)) p0004 p0005
  have p0007 :=
    @g_con2i (.classEq (.cv z) (syn_c0c)) (.classMem (.cv z) (syn_cphi A)) p0006
  have p0008 :=
    @g_a1i (.imp (.classMem (.cv z) (syn_cphi A)) (.neg (.classEq (.cv z) (syn_c0c))))
      (.classEq (syn_cun (syn_cphi A) (syn_csn (syn_c0c)))
        (syn_cun (syn_cphi B) (syn_csn (syn_c0c))))
      p0007
  have p0009 := @g_elun (.cv z) (syn_cphi B) (syn_csn (syn_c0c))
  have p0010 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sn z (syn_c0c)
      dv_cache_0001
  have p0011 := @g_eqabri (.classEq (.cv z) (syn_c0c)) z (syn_csn (syn_c0c)) p0010
  have p0012 :=
    @g_orbi2i (.classMem (.cv z) (syn_csn (syn_c0c))) (.classEq (.cv z) (syn_c0c))
      (.classMem (.cv z) (syn_cphi B)) p0011
  have p0013 :=
    @g_bitri (.classMem (.cv z) (syn_cun (syn_cphi B) (syn_csn (syn_c0c))))
      (syn_wo (.classMem (.cv z) (syn_cphi B)) (.classMem (.cv z) (syn_csn (syn_c0c))))
      (syn_wo (.classMem (.cv z) (syn_cphi B)) (.classEq (.cv z) (syn_c0c))) p0009 p0012
  have p0014 :=
    @g_biimpi (.classMem (.cv z) (syn_cun (syn_cphi B) (syn_csn (syn_c0c))))
      (syn_wo (.classMem (.cv z) (syn_cphi B)) (.classEq (.cv z) (syn_c0c))) p0013
  have p0015 :=
    @g_orcomd (.classMem (.cv z) (syn_cun (syn_cphi B) (syn_csn (syn_c0c))))
      (.classMem (.cv z) (syn_cphi B)) (.classEq (.cv z) (syn_c0c)) p0014
  have p0016 :=
    @g_ord (.classMem (.cv z) (syn_cun (syn_cphi B) (syn_csn (syn_c0c))))
      (.classEq (.cv z) (syn_c0c)) (.classMem (.cv z) (syn_cphi B)) p0015
  have p0017 :=
    @g_ee22
      (.classEq (syn_cun (syn_cphi A) (syn_csn (syn_c0c)))
        (syn_cun (syn_cphi B) (syn_csn (syn_c0c))))
      (.classMem (.cv z) (syn_cphi A))
      (.classMem (.cv z) (syn_cun (syn_cphi B) (syn_csn (syn_c0c))))
      (.neg (.classEq (.cv z) (syn_c0c))) (.classMem (.cv z) (syn_cphi B)) p0003 p0008
      p0016
  have p0018 :=
    @g_ssrdv
      (.classEq (syn_cun (syn_cphi A) (syn_csn (syn_c0c)))
        (syn_cun (syn_cphi B) (syn_csn (syn_c0c))))
      z (syn_cphi A) (syn_cphi B) dv_cache_0002 dv_cache_0003 dv_cache_0004 p0017
  exact p0018

@[expose]
noncomputable def g_phi011 (A : Class) (B : Class) :
    Nominal.NPrf
      (syn_wb (.classEq A B) (.classEq (syn_cun (syn_cphi A) (syn_csn (syn_c0c)))
          (syn_cun (syn_cphi B) (syn_csn (syn_c0c))))) :=
  by
  have p0000 := @g_phi11 A B
  have p0001 := @g_uneq1 (syn_cphi A) (syn_cphi B) (syn_csn (syn_c0c))
  have p0002 := @g_phi011lem1 A B
  have p0003 := @g_phi011lem1 B A
  have p0004 :=
    @g_eqcoms (syn_wss (syn_cphi B) (syn_cphi A))
      (syn_cun (syn_cphi B) (syn_csn (syn_c0c)))
      (syn_cun (syn_cphi A) (syn_csn (syn_c0c))) p0003
  have p0005 :=
    @g_eqssd
      (.classEq (syn_cun (syn_cphi A) (syn_csn (syn_c0c)))
        (syn_cun (syn_cphi B) (syn_csn (syn_c0c))))
      (syn_cphi A) (syn_cphi B) p0002 p0004
  have p0006 :=
    @g_impbii (.classEq (syn_cphi A) (syn_cphi B))
      (.classEq (syn_cun (syn_cphi A) (syn_csn (syn_c0c)))
        (syn_cun (syn_cphi B) (syn_csn (syn_c0c))))
      p0001 p0005
  have p0007 :=
    @g_bitri (.classEq A B) (.classEq (syn_cphi A) (syn_cphi B))
      (.classEq (syn_cun (syn_cphi A) (syn_csn (syn_c0c)))
        (syn_cun (syn_cphi B) (syn_csn (syn_c0c))))
      p0000 p0006
  exact p0007

@[expose]
noncomputable def g_proj1op (A : Class) (B : Class) :
    Nominal.NPrf (.classEq (syn_cproj1 (syn_cop A B)) A) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let z : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let x : Var := freshVar proofSupport 2
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (h))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_z_ne_y : z ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_z : y ≠ z := Ne.symm fresh_z_ne_y
  have fresh_z_ne_x : z ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_y_ne_x : y ≠ x :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have dv_cache_0001 : x ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0002 : y ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0003 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_B, not_false_eq_true])
  have dv_cache_0004 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_B, not_false_eq_true])
  have dv_cache_0005 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0006 : y ∉ ((Wff.classEq (.cv x) (syn_cphi (.cv z)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cphi, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_x, fresh_y_ne_z, or_false, not_false_eq_true])
  have dv_cache_0007 : y ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_z, not_false_eq_true])
  have dv_cache_0008 : x ∉ ((syn_cphi (.cv z))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cphi,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_x_ne_z,
          not_false_eq_true])
  have dv_cache_0009 : x ∉ ((Wff.classMem (.cv z) A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_z, fresh_x_not_A, or_false, not_false_eq_true])
  have dv_cache_0010 :
    x ∉
      ((syn_wrex y B (.classEq (syn_cphi (.cv z))
            (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cphi,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_x_not_B, fresh_x_ne_z,
          fresh_x_ne_y, compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0011 : x ∉ ((syn_cop A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true])
  have dv_cache_0012 : x ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_z, not_false_eq_true])
  have dv_cache_0013 : x ∉ ((Wff.classMem (syn_cphi (.cv z)) (syn_cop A B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cphi,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_z, fresh_x_not_A, fresh_x_not_B, or_false,
          not_false_eq_true])
  have dv_cache_0014 : z ∉ ((syn_cproj1 (syn_cop A B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cproj1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          fresh_z_not_A, fresh_z_not_B, or_false, not_false_eq_true])
  have dv_cache_0015 : z ∉ (A).fv :=
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
        simp only [fresh_z_not_A, not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_op x y A B
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0001 :=
    @g_eleq2i (syn_cop A B)
      (syn_cun (.cab x (syn_wrex y A (.classEq (.cv x) (syn_cphi (.cv y))))) (.cab x
          (syn_wrex y B (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c)))))))
      (syn_cphi (.cv z)) p0000
  have p0002 :=
    @g_elun (syn_cphi (.cv z))
      (.cab x (syn_wrex y A (.classEq (.cv x) (syn_cphi (.cv y)))))
      (.cab x (syn_wrex y B
          (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))))))
  have p0003 := @g_vex z
  have p0004 := @g_phiex (.cv z) p0003
  have p0005 := @g_eqeq1 (.cv x) (syn_cphi (.cv z)) (syn_cphi (.cv y))
  have p0006 := @g_phi11 (.cv z) (.cv y)
  have p0007 := @g_equcom z y
  have p0008_e00_recanon :
    Nominal.NPrf (syn_wb (.objEq z y) (.classEq (syn_cphi (.cv z)) (syn_cphi (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cphi syn_wrex syn_wex syn_wa syn_cif syn_wo syn_cnnc syn_cint
          syn_cplc syn_c1c
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0006
  have p0008 :=
    @g_bitr3i (.classEq (syn_cphi (.cv z)) (syn_cphi (.cv y))) (.objEq z y) (.objEq y z)
      p0008_e00_recanon p0007
  have p0009 :=
    @g_syl6bb (.classEq (.cv x) (syn_cphi (.cv z))) (.classEq (.cv x) (syn_cphi (.cv y)))
      (.classEq (syn_cphi (.cv z)) (syn_cphi (.cv y))) (.objEq y z) p0005 p0008
  have p0010 :=
    @g_rexbidv (.classEq (.cv x) (syn_cphi (.cv z))) (.classEq (.cv x) (syn_cphi (.cv y)))
      (.objEq y z) y A dv_cache_0006 p0009
  have p0011 := @g_risset y (.cv z) A dv_cache_0007 dv_cache_0002
  have p0012_e01_recanon :
    Nominal.NPrf (syn_wb (.classMem (.cv z) A) (syn_wrex y A (.objEq y z))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb, syn_wrex, syn_wex, syn_wa]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0011
  have p0012 :=
    @g_syl6bbr (.classEq (.cv x) (syn_cphi (.cv z)))
      (syn_wrex y A (.classEq (.cv x) (syn_cphi (.cv y)))) (syn_wrex y A (.objEq y z))
      (.classMem (.cv z) A) p0010 p0012_e01_recanon
  have p0013 :=
    @g_elab (syn_wrex y A (.classEq (.cv x) (syn_cphi (.cv y)))) (.classMem (.cv z) A) x
      (syn_cphi (.cv z)) dv_cache_0008 dv_cache_0009 p0004 p0012
  have p0014 :=
    @g_eqeq1 (.cv x) (syn_cphi (.cv z)) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c)))
  have p0015 :=
    @g_rexbidv (.classEq (.cv x) (syn_cphi (.cv z)))
      (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))))
      (.classEq (syn_cphi (.cv z)) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c)))) y B
      dv_cache_0006 p0014
  have p0016 :=
    @g_elab
      (syn_wrex y B (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c)))))
      (syn_wrex y B
        (.classEq (syn_cphi (.cv z)) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c)))))
      x (syn_cphi (.cv z)) dv_cache_0008 dv_cache_0010 p0004 p0015
  have p0017 :=
    @g_orbi12i
      (.classMem (syn_cphi (.cv z))
        (.cab x (syn_wrex y A (.classEq (.cv x) (syn_cphi (.cv y))))))
      (.classMem (.cv z) A)
      (.classMem (syn_cphi (.cv z)) (.cab x (syn_wrex y B
            (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c)))))))
      (syn_wrex y B
        (.classEq (syn_cphi (.cv z)) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c)))))
      p0013 p0016
  have p0018 :=
    @g_n_3bitri (.classMem (syn_cphi (.cv z)) (syn_cop A B))
      (.classMem (syn_cphi (.cv z))
        (syn_cun (.cab x (syn_wrex y A (.classEq (.cv x) (syn_cphi (.cv y))))) (.cab x
            (syn_wrex y B
              (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))))))))
      (syn_wo (.classMem (syn_cphi (.cv z))
          (.cab x (syn_wrex y A (.classEq (.cv x) (syn_cphi (.cv y))))))
        (.classMem (syn_cphi (.cv z)) (.cab x (syn_wrex y B
              (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))))))))
      (syn_wo (.classMem (.cv z) A) (syn_wrex y B
          (.classEq (syn_cphi (.cv z)) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))))))
      p0001 p0002 p0017
  have p0019 := @g_phieq (.cv x) (.cv z)
  have p0020_e00_recanon :
    Nominal.NPrf (.imp (.objEq x z) (.classEq (syn_cphi (.cv x)) (syn_cphi (.cv z)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cphi syn_wrex syn_wex syn_wa syn_cif syn_wo syn_cnnc syn_cint syn_cplc
          syn_c1c
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0019
  have p0020 :=
    @g_eleq1d (.objEq x z) (syn_cphi (.cv x)) (syn_cphi (.cv z)) (syn_cop A B)
      p0020_e00_recanon
  have p0021 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_proj1 x
      (syn_cop A B) dv_cache_0011
  have p0022_e01_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv x) (.cv z)) (syn_wb (.classMem (syn_cphi (.cv x)) (syn_cop A B))
          (.classMem (syn_cphi (.cv z)) (syn_cop A B)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cphi syn_wrex syn_wex syn_wa syn_cif syn_wo syn_cnnc syn_cint
          syn_cplc syn_c1c syn_cop syn_cun syn_cnin syn_wnan syn_ccompl
        simp (config :=
          {
            failIfUnchanged :=
              false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0020
  have p0022 :=
    @g_elab2 (.classMem (syn_cphi (.cv x)) (syn_cop A B))
      (.classMem (syn_cphi (.cv z)) (syn_cop A B)) x (.cv z) (syn_cproj1 (syn_cop A B))
      dv_cache_0012 dv_cache_0013 p0003 p0022_e01_recanon p0021
  have p0023 := @g_n_0cnelphi (.cv z)
  have p0024 := @g_ssun2 (syn_csn (syn_c0c)) (syn_cphi (.cv y))
  have p0025 := @g_n_0cex
  have p0026 := @g_snid (syn_c0c) p0025
  have p0027 :=
    @g_sselii (syn_csn (syn_c0c)) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c)))
      (syn_c0c) p0024 p0026
  have p0028 :=
    @g_eleq2 (syn_cphi (.cv z)) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))) (syn_c0c)
  have p0029 :=
    @g_mpbiri
      (.classEq (syn_cphi (.cv z)) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))))
      (.classMem (syn_c0c) (syn_cphi (.cv z)))
      (.classMem (syn_c0c) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c)))) p0027 p0028
  have p0030 :=
    @g_mto (.classEq (syn_cphi (.cv z)) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))))
      (.classMem (syn_c0c) (syn_cphi (.cv z))) p0023 p0029
  have p0031 :=
    @g_a1i
      (.neg (.classEq (syn_cphi (.cv z)) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c)))))
      (.classMem (.cv y) B) p0030
  have p0032 :=
    @g_nrex (.classEq (syn_cphi (.cv z)) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))))
      y B p0031
  have p0033 :=
    @g_biorfi
      (syn_wrex y B
        (.classEq (syn_cphi (.cv z)) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c)))))
      (.classMem (.cv z) A) p0032
  have p0034 :=
    @g_n_3bitr4i (.classMem (syn_cphi (.cv z)) (syn_cop A B))
      (syn_wo (.classMem (.cv z) A) (syn_wrex y B
          (.classEq (syn_cphi (.cv z)) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))))))
      (.classMem (.cv z) (syn_cproj1 (syn_cop A B))) (.classMem (.cv z) A) p0018 p0022
      p0033
  have p0035 := @g_eqriv z (syn_cproj1 (syn_cop A B)) A dv_cache_0014 dv_cache_0015 p0034
  exact p0035

@[expose]
noncomputable def g_proj2op (A : Class) (B : Class) :
    Nominal.NPrf (.classEq (syn_cproj2 (syn_cop A B)) B) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let z : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let x : Var := freshVar proofSupport 2
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (h))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_z_ne_y : z ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_z : y ≠ z := Ne.symm fresh_z_ne_y
  have fresh_z_ne_x : z ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_y_ne_x : y ≠ x :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have dv_cache_0001 : x ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0002 : y ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0003 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_B, not_false_eq_true])
  have dv_cache_0004 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_B, not_false_eq_true])
  have dv_cache_0005 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0006 :
    y ∉ ((Wff.classEq (.cv x) (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cphi,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_x, fresh_y_ne_z, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ ((syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cphi,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_z, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0008 :
    x ∉
      ((syn_wrex y A (.classEq (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c)))
            (syn_cphi (.cv y))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cphi,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_x_not_A, fresh_x_ne_z,
          fresh_x_ne_y, compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0009 :
    x ∉
      ((syn_wrex y B (.classEq (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c)))
            (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cphi,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_x_not_B, fresh_x_ne_z,
          fresh_x_ne_y, compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0010 : y ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_z, not_false_eq_true])
  have dv_cache_0011 : x ∉ ((syn_cop A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true])
  have dv_cache_0012 : x ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_z, not_false_eq_true])
  have dv_cache_0013 :
    x ∉
      ((Wff.classMem (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c))) (syn_cop A B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cphi,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_z, fresh_x_not_A, fresh_x_not_B,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0014 : z ∉ ((syn_cproj2 (syn_cop A B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cproj2,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          fresh_z_not_A, fresh_z_not_B, or_false, not_false_eq_true])
  have dv_cache_0015 : z ∉ (B).fv :=
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
        simp only [fresh_z_not_B, not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_op x y A B
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0001 :=
    @g_eleq2i (syn_cop A B)
      (syn_cun (.cab x (syn_wrex y A (.classEq (.cv x) (syn_cphi (.cv y))))) (.cab x
          (syn_wrex y B (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c)))))))
      (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c))) p0000
  have p0002 :=
    @g_elun (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c)))
      (.cab x (syn_wrex y A (.classEq (.cv x) (syn_cphi (.cv y)))))
      (.cab x (syn_wrex y B
          (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))))))
  have p0003 := @g_vex z
  have p0004 := @g_phiex (.cv z) p0003
  have p0005 := @g_snex (syn_c0c)
  have p0006 := @g_unex (syn_cphi (.cv z)) (syn_csn (syn_c0c)) p0004 p0005
  have p0007 :=
    @g_eqeq1 (.cv x) (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c))) (syn_cphi (.cv y))
  have p0008 :=
    @g_rexbidv (.classEq (.cv x) (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c))))
      (.classEq (.cv x) (syn_cphi (.cv y)))
      (.classEq (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c))) (syn_cphi (.cv y))) y A
      dv_cache_0006 p0007
  have p0009 :=
    @g_elab (syn_wrex y A (.classEq (.cv x) (syn_cphi (.cv y))))
      (syn_wrex y A
        (.classEq (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c))) (syn_cphi (.cv y))))
      x (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c))) dv_cache_0007 dv_cache_0008 p0006
      p0008
  have p0010 := @g_phi011 (.cv z) (.cv y)
  have p0011 := @g_equcom z y
  have p0012_e00_recanon :
    Nominal.NPrf
      (syn_wb (.objEq z y) (.classEq (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c)))
          (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_cphi syn_wrex
          syn_wex syn_cif syn_wo syn_cnnc syn_cint syn_cplc syn_c1c syn_csn syn_c0c
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0010
  have p0012 :=
    @g_bitr3i
      (.classEq (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c)))
        (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))))
      (.objEq z y) (.objEq y z) p0012_e00_recanon p0011
  have p0013 :=
    @g_rexbii
      (.classEq (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c)))
        (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))))
      (.objEq y z) y B p0012
  have p0014 :=
    @g_eqeq1 (.cv x) (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c)))
      (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c)))
  have p0015 :=
    @g_rexbidv (.classEq (.cv x) (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c))))
      (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))))
      (.classEq (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c)))
        (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))))
      y B dv_cache_0006 p0014
  have p0016 :=
    @g_elab
      (syn_wrex y B (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c)))))
      (syn_wrex y B (.classEq (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c)))
          (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c)))))
      x (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c))) dv_cache_0007 dv_cache_0009 p0006
      p0015
  have p0017 := @g_risset y (.cv z) B dv_cache_0010 dv_cache_0004
  have p0018_e02_recanon :
    Nominal.NPrf (syn_wb (.classMem (.cv z) B) (syn_wrex y B (.objEq y z))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb, syn_wrex, syn_wex, syn_wa]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0017
  have p0018 :=
    @g_n_3bitr4i
      (syn_wrex y B (.classEq (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c)))
          (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c)))))
      (syn_wrex y B (.objEq y z))
      (.classMem (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c))) (.cab x (syn_wrex y B
            (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c)))))))
      (.classMem (.cv z) B) p0013 p0016 p0018_e02_recanon
  have p0019 :=
    @g_orbi12i
      (.classMem (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c)))
        (.cab x (syn_wrex y A (.classEq (.cv x) (syn_cphi (.cv y))))))
      (syn_wrex y A
        (.classEq (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c))) (syn_cphi (.cv y))))
      (.classMem (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c))) (.cab x (syn_wrex y B
            (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c)))))))
      (.classMem (.cv z) B) p0009 p0018
  have p0020 :=
    @g_bitri
      (.classMem (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c)))
        (syn_cun (.cab x (syn_wrex y A (.classEq (.cv x) (syn_cphi (.cv y))))) (.cab x
            (syn_wrex y B
              (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))))))))
      (syn_wo (.classMem (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c)))
          (.cab x (syn_wrex y A (.classEq (.cv x) (syn_cphi (.cv y))))))
        (.classMem (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c))) (.cab x (syn_wrex y B
              (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))))))))
      (syn_wo (syn_wrex y A
          (.classEq (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c))) (syn_cphi (.cv y))))
        (.classMem (.cv z) B))
      p0002 p0019
  have p0021 :=
    @g_bitri (.classMem (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c))) (syn_cop A B))
      (.classMem (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c)))
        (syn_cun (.cab x (syn_wrex y A (.classEq (.cv x) (syn_cphi (.cv y))))) (.cab x
            (syn_wrex y B
              (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))))))))
      (syn_wo (syn_wrex y A
          (.classEq (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c))) (syn_cphi (.cv y))))
        (.classMem (.cv z) B))
      p0001 p0020
  have p0022 := @g_phieq (.cv x) (.cv z)
  have p0023_e00_recanon :
    Nominal.NPrf (.imp (.objEq x z) (.classEq (syn_cphi (.cv x)) (syn_cphi (.cv z)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cphi syn_wrex syn_wex syn_wa syn_cif syn_wo syn_cnnc syn_cint syn_cplc
          syn_c1c
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0022
  have p0023 :=
    @g_uneq1d (.objEq x z) (syn_cphi (.cv x)) (syn_cphi (.cv z)) (syn_csn (syn_c0c))
      p0023_e00_recanon
  have p0024 :=
    @g_eleq1d (.objEq x z) (syn_cun (syn_cphi (.cv x)) (syn_csn (syn_c0c)))
      (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c))) (syn_cop A B) p0023
  have p0025 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_proj2 x
      (syn_cop A B) dv_cache_0011
  have p0026_e01_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv x) (.cv z))
        (syn_wb (.classMem (syn_cun (syn_cphi (.cv x)) (syn_csn (syn_c0c))) (syn_cop A B))
          (.classMem (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c))) (syn_cop A B)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_cphi syn_wrex
          syn_wex syn_cif syn_wo syn_cnnc syn_cint syn_cplc syn_c1c syn_csn syn_c0c
          syn_cop
        simp (config :=
          {
            failIfUnchanged :=
              false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0024
  have p0026 :=
    @g_elab2 (.classMem (syn_cun (syn_cphi (.cv x)) (syn_csn (syn_c0c))) (syn_cop A B))
      (.classMem (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c))) (syn_cop A B)) x (.cv z)
      (syn_cproj2 (syn_cop A B)) dv_cache_0012 dv_cache_0013 p0003 p0026_e01_recanon p0025
  have p0027 := @g_n_0cnelphi (.cv y)
  have p0028 := @g_ssun2 (syn_csn (syn_c0c)) (syn_cphi (.cv z))
  have p0029 := @g_n_0cex
  have p0030 := @g_snid (syn_c0c) p0029
  have p0031 :=
    @g_sselii (syn_csn (syn_c0c)) (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c)))
      (syn_c0c) p0028 p0030
  have p0032 :=
    @g_eleq2 (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c))) (syn_cphi (.cv y)) (syn_c0c)
  have p0033 :=
    @g_mpbii
      (.classEq (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c))) (syn_cphi (.cv y)))
      (.classMem (syn_c0c) (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c))))
      (.classMem (syn_c0c) (syn_cphi (.cv y))) p0031 p0032
  have p0034 :=
    @g_mto (.classEq (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c))) (syn_cphi (.cv y)))
      (.classMem (syn_c0c) (syn_cphi (.cv y))) p0027 p0033
  have p0035 :=
    @g_a1i
      (.neg (.classEq (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c))) (syn_cphi (.cv y))))
      (.classMem (.cv y) A) p0034
  have p0036 :=
    @g_nrex (.classEq (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c))) (syn_cphi (.cv y)))
      y A p0035
  have p0037 :=
    @g_biorfi
      (syn_wrex y A
        (.classEq (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c))) (syn_cphi (.cv y))))
      (.classMem (.cv z) B) p0036
  have p0038 :=
    @g_orcom (.classMem (.cv z) B)
      (syn_wrex y A
        (.classEq (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c))) (syn_cphi (.cv y))))
  have p0039 :=
    @g_bitri (.classMem (.cv z) B)
      (syn_wo (.classMem (.cv z) B) (syn_wrex y A
          (.classEq (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c))) (syn_cphi (.cv y)))))
      (syn_wo (syn_wrex y A
          (.classEq (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c))) (syn_cphi (.cv y))))
        (.classMem (.cv z) B))
      p0037 p0038
  have p0040 :=
    @g_n_3bitr4i
      (.classMem (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c))) (syn_cop A B))
      (syn_wo (syn_wrex y A
          (.classEq (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c))) (syn_cphi (.cv y))))
        (.classMem (.cv z) B))
      (.classMem (.cv z) (syn_cproj2 (syn_cop A B))) (.classMem (.cv z) B) p0021 p0026
      p0039
  have p0041 := @g_eqriv z (syn_cproj2 (syn_cop A B)) B dv_cache_0014 dv_cache_0015 p0040
  exact p0041

@[expose]
noncomputable def g_opth (A : Class) (B : Class) (C : Class) (D : Class) :
    Nominal.NPrf
      (syn_wb (.classEq (syn_cop A B) (syn_cop C D)) (syn_wa (.classEq A C) (.classEq B D))) :=
  by
  have p0000 := @g_proj1eq (syn_cop A B) (syn_cop C D)
  have p0001 := @g_proj1op A B
  have p0002 := @g_proj1op C D
  have p0003 :=
    @g_n_3eqtr3g (.classEq (syn_cop A B) (syn_cop C D)) (syn_cproj1 (syn_cop A B))
      (syn_cproj1 (syn_cop C D)) A C p0000 p0001 p0002
  have p0004 := @g_proj2eq (syn_cop A B) (syn_cop C D)
  have p0005 := @g_proj2op A B
  have p0006 := @g_proj2op C D
  have p0007 :=
    @g_n_3eqtr3g (.classEq (syn_cop A B) (syn_cop C D)) (syn_cproj2 (syn_cop A B))
      (syn_cproj2 (syn_cop C D)) B D p0004 p0005 p0006
  have p0008 :=
    @g_jca (.classEq (syn_cop A B) (syn_cop C D)) (.classEq A C) (.classEq B D) p0003
      p0007
  have p0009 := @g_opeq12 A C B D
  have p0010 :=
    @g_impbii (.classEq (syn_cop A B) (syn_cop C D))
      (syn_wa (.classEq A C) (.classEq B D)) p0008 p0009
  exact p0010

@[expose]
noncomputable def g_opexb (A : Class) (B : Class) :
    Nominal.NPrf
      (syn_wb (.classMem (syn_cop A B) (syn_cvv))
        (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv)))) :=
  by
  have p0000 := @g_proj1op A B
  have p0001 := @g_proj1exg (syn_cop A B) (syn_cvv)
  have p0002 :=
    @g_syl5eqelr (.classMem (syn_cop A B) (syn_cvv)) A (syn_cproj1 (syn_cop A B))
      (syn_cvv) p0000 p0001
  have p0003 := @g_proj2op A B
  have p0004 := @g_proj2exg (syn_cop A B) (syn_cvv)
  have p0005 :=
    @g_syl5eqelr (.classMem (syn_cop A B) (syn_cvv)) B (syn_cproj2 (syn_cop A B))
      (syn_cvv) p0003 p0004
  have p0006 :=
    @g_jca (.classMem (syn_cop A B) (syn_cvv)) (.classMem A (syn_cvv))
      (.classMem B (syn_cvv)) p0002 p0005
  have p0007 := @g_opexg A B (syn_cvv) (syn_cvv)
  have p0008 :=
    @g_impbii (.classMem (syn_cop A B) (syn_cvv))
      (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv))) p0006 p0007
  exact p0008


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk010Compact001Part035`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_nfop (x : Var) (A : Class) (B : Class)
    (hyp_nfop_1 : Nominal.NPrf (syn_wnfc x A))
    (hyp_nfop_2 : Nominal.NPrf (syn_wnfc x B)) :
    Nominal.NPrf (syn_wnfc x (syn_cop A B)) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  let z : Var := freshVar proofSupport 0
  let w : Var := freshVar proofSupport 1
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_w : x ≠ w := Ne.symm fresh_w_ne_x
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_w_not_B : w ∉ B.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have fresh_z_ne_w : z ≠ w :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : z ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_A, not_false_eq_true])
  have dv_cache_0002 : w ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_A, not_false_eq_true])
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
  have dv_cache_0004 : w ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_B, not_false_eq_true])
  have dv_cache_0005 : z ≠ w :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show z ≠ w from (by exact fresh_z_ne_w))
  have dv_cache_0006 : x ∉ ((Wff.classEq (.cv z) (syn_cphi (.cv w)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cphi, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_z, fresh_x_ne_w, or_false, not_false_eq_true])
  have dv_cache_0007 :
    x ∉ ((Wff.classEq (.cv z) (syn_cun (syn_cphi (.cv w)) (syn_csn (syn_c0c))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cphi,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_z, fresh_x_ne_w, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_op z w A B
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0001 := @g_nfv (.classEq (.cv z) (syn_cphi (.cv w))) x dv_cache_0006
  have p0002 := @g_nfrex (.classEq (.cv z) (syn_cphi (.cv w))) x w A hyp_nfop_1 p0001
  have p0003 := @g_nfab (syn_wrex w A (.classEq (.cv z) (syn_cphi (.cv w)))) x z p0002
  have p0004 :=
    @g_nfv (.classEq (.cv z) (syn_cun (syn_cphi (.cv w)) (syn_csn (syn_c0c)))) x
      dv_cache_0007
  have p0005 :=
    @g_nfrex (.classEq (.cv z) (syn_cun (syn_cphi (.cv w)) (syn_csn (syn_c0c)))) x w B
      hyp_nfop_2 p0004
  have p0006 :=
    @g_nfab
      (syn_wrex w B (.classEq (.cv z) (syn_cun (syn_cphi (.cv w)) (syn_csn (syn_c0c))))) x
      z p0005
  have p0007 :=
    @g_nfun x (.cab z (syn_wrex w A (.classEq (.cv z) (syn_cphi (.cv w)))))
      (.cab z (syn_wrex w B
          (.classEq (.cv z) (syn_cun (syn_cphi (.cv w)) (syn_csn (syn_c0c))))))
      p0003 p0006
  have p0008 :=
    @g_nfcxfr x (syn_cop A B)
      (syn_cun (.cab z (syn_wrex w A (.classEq (.cv z) (syn_cphi (.cv w))))) (.cab z
          (syn_wrex w B (.classEq (.cv z) (syn_cun (syn_cphi (.cv w)) (syn_csn (syn_c0c)))))))
      p0000 p0007
  exact p0008

@[expose]
noncomputable def g_nfopd (ph : Wff) (x : Var) (A : Class) (B : Class)
    (hyp_nfopd_1 : Nominal.NPrf (.imp ph (syn_wnfc x A)))
    (hyp_nfopd_2 : Nominal.NPrf (.imp ph (syn_wnfc x B))) :
    Nominal.NPrf (.imp ph (syn_wnfc x (syn_cop A B))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have dv_cache_0001 : z ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_A, not_false_eq_true])
  have dv_cache_0002 : x ≠ z := by
    clear dv_cache_0001
    exact (show x ≠ z from (by exact fresh_x_ne_z))
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
  have p0000 := @g_nfaba1 (.classMem (.cv z) A) x z
  have p0001 := @g_nfaba1 (.classMem (.cv z) B) x z
  have p0002 :=
    @g_nfop x (.cab z (.all x (.classMem (.cv z) A)))
      (.cab z (.all x (.classMem (.cv z) B))) p0000 p0001
  have p0003 := @g_nfnfc1 x A
  have p0004 := @g_nfnfc1 x B
  have p0005 := @g_nfan (syn_wnfc x A) (syn_wnfc x B) x p0003 p0004
  have p0006 := @g_abidnf x z A dv_cache_0001 dv_cache_0002
  have p0007 :=
    @g_adantr (syn_wnfc x A) (.classEq (.cab z (.all x (.classMem (.cv z) A))) A)
      (syn_wnfc x B) p0006
  have p0008 := @g_abidnf x z B dv_cache_0003 dv_cache_0002
  have p0009 :=
    @g_adantl (syn_wnfc x B) (.classEq (.cab z (.all x (.classMem (.cv z) B))) B)
      (syn_wnfc x A) p0008
  have p0010 :=
    @g_opeq12d (syn_wa (syn_wnfc x A) (syn_wnfc x B))
      (.cab z (.all x (.classMem (.cv z) A))) A (.cab z (.all x (.classMem (.cv z) B))) B
      p0007 p0009
  have p0011 :=
    @g_nfceqdf (syn_wa (syn_wnfc x A) (syn_wnfc x B)) x
      (syn_cop (.cab z (.all x (.classMem (.cv z) A))) (.cab z (.all x (.classMem (.cv z) B))))
      (syn_cop A B) p0005 p0010
  have p0012 :=
    @g_syl2anc ph (syn_wnfc x A) (syn_wnfc x B)
      (syn_wb (syn_wnfc x (syn_cop (.cab z (.all x (.classMem (.cv z) A)))
            (.cab z (.all x (.classMem (.cv z) B))))) (syn_wnfc x (syn_cop A B)))
      hyp_nfopd_1 hyp_nfopd_2 p0011
  have p0013 :=
    @g_mpbii ph
      (syn_wnfc x (syn_cop (.cab z (.all x (.classMem (.cv z) A)))
          (.cab z (.all x (.classMem (.cv z) B)))))
      (syn_wnfc x (syn_cop A B)) p0002 p0012
  exact p0013

@[expose]
noncomputable def g_eqvinop (x : Var) (y : Var) (A : Class) (B : Class) (C : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv)
    (dv_C_x : x ∉ C.fv) (dv_C_y : y ∉ C.fv) (dv_x_y : x ≠ y)
    (hyp_eqvinop_1 : Nominal.NPrf (.classMem B (syn_cvv)))
    (hyp_eqvinop_2 : Nominal.NPrf (.classMem C (syn_cvv))) :
    Nominal.NPrf
      (syn_wb (.classEq A (syn_cop B C)) (syn_wex x (syn_wex y
            (syn_wa (.classEq A (syn_cop (.cv x) (.cv y)))
              (.classEq (syn_cop (.cv x) (.cv y)) (syn_cop B C)))))) :=
  by
  have dv_cache_0001 : y ∉ ((Wff.classEq (.cv x) B)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_x_y), dv_B_y, or_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (C).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_y, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((Wff.classEq A (syn_cop (.cv x) C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_A_y, (Ne.symm dv_x_y), dv_C_y, or_false,
          not_false_eq_true])
  have dv_cache_0004 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_x, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((Wff.classEq A (syn_cop B C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union, dv_A_x,
          dv_B_x, dv_C_x, or_false, not_false_eq_true])
  have p0000 := @g_opth (.cv x) (.cv y) B C
  have p0001 := @g_ancom (.classEq (.cv x) B) (.classEq (.cv y) C)
  have p0002 :=
    @g_bitri (.classEq (syn_cop (.cv x) (.cv y)) (syn_cop B C))
      (syn_wa (.classEq (.cv x) B) (.classEq (.cv y) C))
      (syn_wa (.classEq (.cv y) C) (.classEq (.cv x) B)) p0000 p0001
  have p0003 :=
    @g_anbi2i (.classEq (syn_cop (.cv x) (.cv y)) (syn_cop B C))
      (syn_wa (.classEq (.cv y) C) (.classEq (.cv x) B))
      (.classEq A (syn_cop (.cv x) (.cv y))) p0002
  have p0004 :=
    @g_an13 (.classEq A (syn_cop (.cv x) (.cv y))) (.classEq (.cv y) C)
      (.classEq (.cv x) B)
  have p0005 :=
    @g_bitri
      (syn_wa (.classEq A (syn_cop (.cv x) (.cv y)))
        (.classEq (syn_cop (.cv x) (.cv y)) (syn_cop B C)))
      (syn_wa (.classEq A (syn_cop (.cv x) (.cv y)))
        (syn_wa (.classEq (.cv y) C) (.classEq (.cv x) B)))
      (syn_wa (.classEq (.cv x) B)
        (syn_wa (.classEq (.cv y) C) (.classEq A (syn_cop (.cv x) (.cv y)))))
      p0003 p0004
  have p0006 :=
    @g_exbii
      (syn_wa (.classEq A (syn_cop (.cv x) (.cv y)))
        (.classEq (syn_cop (.cv x) (.cv y)) (syn_cop B C)))
      (syn_wa (.classEq (.cv x) B)
        (syn_wa (.classEq (.cv y) C) (.classEq A (syn_cop (.cv x) (.cv y)))))
      y p0005
  have p0007 :=
    @g_n_19_42v (.classEq (.cv x) B)
      (syn_wa (.classEq (.cv y) C) (.classEq A (syn_cop (.cv x) (.cv y)))) y dv_cache_0001
  have p0008 := @g_opeq2 (.cv y) C (.cv x)
  have p0009 :=
    @g_eqeq2d (.classEq (.cv y) C) (syn_cop (.cv x) (.cv y)) (syn_cop (.cv x) C) A p0008
  have p0010 :=
    @g_ceqsexv (.classEq A (syn_cop (.cv x) (.cv y))) (.classEq A (syn_cop (.cv x) C)) y C
      dv_cache_0002 dv_cache_0003 hyp_eqvinop_2 p0009
  have p0011 :=
    @g_anbi2i
      (syn_wex y (syn_wa (.classEq (.cv y) C) (.classEq A (syn_cop (.cv x) (.cv y)))))
      (.classEq A (syn_cop (.cv x) C)) (.classEq (.cv x) B) p0010
  have p0012 :=
    @g_n_3bitri
      (syn_wex y (syn_wa (.classEq A (syn_cop (.cv x) (.cv y)))
          (.classEq (syn_cop (.cv x) (.cv y)) (syn_cop B C))))
      (syn_wex y (syn_wa (.classEq (.cv x) B)
          (syn_wa (.classEq (.cv y) C) (.classEq A (syn_cop (.cv x) (.cv y))))))
      (syn_wa (.classEq (.cv x) B)
        (syn_wex y (syn_wa (.classEq (.cv y) C) (.classEq A (syn_cop (.cv x) (.cv y))))))
      (syn_wa (.classEq (.cv x) B) (.classEq A (syn_cop (.cv x) C))) p0006 p0007 p0011
  have p0013 :=
    @g_exbii
      (syn_wex y (syn_wa (.classEq A (syn_cop (.cv x) (.cv y)))
          (.classEq (syn_cop (.cv x) (.cv y)) (syn_cop B C))))
      (syn_wa (.classEq (.cv x) B) (.classEq A (syn_cop (.cv x) C))) x p0012
  have p0014 := @g_opeq1 (.cv x) B C
  have p0015 := @g_eqeq2d (.classEq (.cv x) B) (syn_cop (.cv x) C) (syn_cop B C) A p0014
  have p0016 :=
    @g_ceqsexv (.classEq A (syn_cop (.cv x) C)) (.classEq A (syn_cop B C)) x B
      dv_cache_0004 dv_cache_0005 hyp_eqvinop_1 p0015
  have p0017 :=
    @g_bitr2i
      (syn_wex x (syn_wex y (syn_wa (.classEq A (syn_cop (.cv x) (.cv y)))
            (.classEq (syn_cop (.cv x) (.cv y)) (syn_cop B C)))))
      (syn_wex x (syn_wa (.classEq (.cv x) B) (.classEq A (syn_cop (.cv x) C))))
      (.classEq A (syn_cop B C)) p0013 p0016
  exact p0017

@[expose]
noncomputable def g_copsexg (ph : Wff) (x : Var) (y : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) :
    Nominal.NPrf
      (.imp (.classEq A (syn_cop (.cv x) (.cv y))) (syn_wb ph
          (syn_wex x (syn_wex y (syn_wa (.classEq A (syn_cop (.cv x) (.cv y))) ph))))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv
  let z : Var := freshVar proofSupport 0
  let w : Var := freshVar proofSupport 1
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_not_ph : z ∉ ph.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_y_ne_z : y ≠ z := Ne.symm fresh_z_ne_y
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_w_not_ph : w ∉ ph.fv := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_w : x ≠ w := Ne.symm fresh_w_ne_x
  have fresh_w_ne_y : w ≠ y := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_y_ne_w : y ≠ w := Ne.symm fresh_w_ne_y
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have fresh_z_ne_w : z ≠ w :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : z ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_A, not_false_eq_true])
  have dv_cache_0002 : w ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_A, not_false_eq_true])
  have dv_cache_0003 : z ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_x, not_false_eq_true])
  have dv_cache_0004 : w ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_w_ne_x, not_false_eq_true])
  have dv_cache_0005 : z ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_y, not_false_eq_true])
  have dv_cache_0006 : w ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_w_ne_y, not_false_eq_true])
  have dv_cache_0007 : z ≠ w :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show z ≠ w from (by exact fresh_z_ne_w))
  have dv_cache_0008 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0009 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0010 : y ≠ w :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show y ≠ w from (by exact fresh_y_ne_w))
  have dv_cache_0011 : x ∉ ((Wff.classEq A (syn_cop (.cv z) (.cv w)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_A_x, fresh_x_ne_z, fresh_x_ne_w, or_false,
          not_false_eq_true])
  have dv_cache_0012 : y ∉ ((Wff.classEq A (syn_cop (.cv z) (.cv w)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_A_y, fresh_y_ne_z, fresh_y_ne_w, or_false,
          not_false_eq_true])
  have dv_cache_0013 :
    z ∉
      ((Wff.imp (.classEq A (syn_cop (.cv x) (.cv y))) (syn_wb ph (syn_wex x
              (syn_wex y (syn_wa (.classEq A (syn_cop (.cv x) (.cv y))) ph)))))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_z_not_A, fresh_z_ne_x,
          fresh_z_ne_y, fresh_z_not_ph, or_false, and_false, not_false_eq_true])
  have dv_cache_0014 :
    w ∉
      ((Wff.imp (.classEq A (syn_cop (.cv x) (.cv y))) (syn_wb ph (syn_wex x
              (syn_wex y (syn_wa (.classEq A (syn_cop (.cv x) (.cv y))) ph)))))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_w_not_A, fresh_w_ne_x,
          fresh_w_ne_y, fresh_w_not_ph, or_false, and_false, not_false_eq_true])
  have p0000 := @g_vex x
  have p0001 := @g_vex y
  have p0002 :=
    @g_eqvinop z w A (.cv x) (.cv y) dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 p0000 p0001
  have p0003 :=
    @g_n_19_8a (syn_wa (.classEq (syn_cop (.cv z) (.cv w)) (syn_cop (.cv x) (.cv y))) ph)
      y
  have p0004 :=
    @g_n_19_8a
      (syn_wex y (syn_wa (.classEq (syn_cop (.cv z) (.cv w)) (syn_cop (.cv x) (.cv y))) ph))
      x
  have p0005 :=
    @g_syl (syn_wa (.classEq (syn_cop (.cv z) (.cv w)) (syn_cop (.cv x) (.cv y))) ph)
      (syn_wex y (syn_wa (.classEq (syn_cop (.cv z) (.cv w)) (syn_cop (.cv x) (.cv y))) ph))
      (syn_wex x (syn_wex y
          (syn_wa (.classEq (syn_cop (.cv z) (.cv w)) (syn_cop (.cv x) (.cv y))) ph)))
      p0003 p0004
  have p0006 :=
    @g_ex (.classEq (syn_cop (.cv z) (.cv w)) (syn_cop (.cv x) (.cv y))) ph
      (syn_wex x (syn_wex y
          (syn_wa (.classEq (syn_cop (.cv z) (.cv w)) (syn_cop (.cv x) (.cv y))) ph)))
      p0005
  have p0007 := @g_opth (.cv z) (.cv w) (.cv x) (.cv y)
  have p0008_e00_recanon :
    Nominal.NPrf
      (syn_wb (.classEq (syn_cop (.cv z) (.cv w)) (syn_cop (.cv x) (.cv y)))
        (syn_wa (.objEq z x) (.objEq w y))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex
          syn_cphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0007
  have p0008 :=
    @g_anbi1i (.classEq (syn_cop (.cv z) (.cv w)) (syn_cop (.cv x) (.cv y)))
      (syn_wa (.objEq z x) (.objEq w y)) ph p0008_e00_recanon
  have p0009 :=
    @g_n_2exbii (syn_wa (.classEq (syn_cop (.cv z) (.cv w)) (syn_cop (.cv x) (.cv y))) ph)
      (syn_wa (syn_wa (.objEq z x) (.objEq w y)) ph) x y p0008
  have p0010 := @g_nfe1 (syn_wa (.objEq z x) (syn_wex y (syn_wa (.objEq w y) ph))) x
  have p0011 := @g_nfae y x y
  have p0012 := @g_anass (.objEq z x) (.objEq w y) ph
  have p0013 := @g_n_19_8a (syn_wa (.objEq w y) ph) y
  have p0014 :=
    @g_a1i (.imp (syn_wa (.objEq w y) ph) (syn_wex y (syn_wa (.objEq w y) ph)))
      (.all y (.objEq y x)) p0013
  have p0015 :=
    @g_anim2d (.all y (.objEq y x)) (syn_wa (.objEq w y) ph)
      (syn_wex y (syn_wa (.objEq w y) ph)) (.objEq z x) p0014
  have p0016 :=
    @g_syl5bi (syn_wa (syn_wa (.objEq z x) (.objEq w y)) ph)
      (syn_wa (.objEq z x) (syn_wa (.objEq w y) ph)) (.all y (.objEq y x))
      (syn_wa (.objEq z x) (syn_wex y (syn_wa (.objEq w y) ph))) p0012 p0015
  have p0017 :=
    @g_eximd (.all y (.objEq y x)) (syn_wa (syn_wa (.objEq z x) (.objEq w y)) ph)
      (syn_wa (.objEq z x) (syn_wex y (syn_wa (.objEq w y) ph))) y p0011 p0016
  have p0018 :=
    @g_biidd (.all y (.objEq y x))
      (syn_wa (.objEq z x) (syn_wex y (syn_wa (.objEq w y) ph)))
  have p0019 :=
    @g_drex1 (syn_wa (.objEq z x) (syn_wex y (syn_wa (.objEq w y) ph)))
      (syn_wa (.objEq z x) (syn_wex y (syn_wa (.objEq w y) ph))) y x p0018
  have p0020 :=
    @g_sylibd (.all y (.objEq y x))
      (syn_wex y (syn_wa (syn_wa (.objEq z x) (.objEq w y)) ph))
      (syn_wex y (syn_wa (.objEq z x) (syn_wex y (syn_wa (.objEq w y) ph))))
      (syn_wex x (syn_wa (.objEq z x) (syn_wex y (syn_wa (.objEq w y) ph)))) p0017 p0019
  have p0021 :=
    @g_exbii (syn_wa (syn_wa (.objEq z x) (.objEq w y)) ph)
      (syn_wa (.objEq z x) (syn_wa (.objEq w y) ph)) y p0012
  have p0022 := @g_n_19_40 (.objEq z x) (syn_wa (.objEq w y) ph) y
  have p0023 := @g_nfnae y x y
  have p0024 := @g_dveeq2 y x z dv_cache_0008
  have p0025 := @g_nfd (.neg (.all y (.objEq y x))) (.objEq z x) y p0023 p0024
  have p0026 := @g_n_19_9d (.objEq z x) (.neg (.all y (.objEq y x))) y p0025
  have p0027 :=
    @g_anim1d (.neg (.all y (.objEq y x))) (syn_wex y (.objEq z x)) (.objEq z x)
      (syn_wex y (syn_wa (.objEq w y) ph)) p0026
  have p0028 :=
    @g_syl5 (syn_wex y (syn_wa (.objEq z x) (syn_wa (.objEq w y) ph)))
      (syn_wa (syn_wex y (.objEq z x)) (syn_wex y (syn_wa (.objEq w y) ph)))
      (.neg (.all y (.objEq y x)))
      (syn_wa (.objEq z x) (syn_wex y (syn_wa (.objEq w y) ph))) p0022 p0027
  have p0029 :=
    @g_syl5bi (syn_wex y (syn_wa (syn_wa (.objEq z x) (.objEq w y)) ph))
      (syn_wex y (syn_wa (.objEq z x) (syn_wa (.objEq w y) ph)))
      (.neg (.all y (.objEq y x)))
      (syn_wa (.objEq z x) (syn_wex y (syn_wa (.objEq w y) ph))) p0021 p0028
  have p0030 := @g_n_19_8a (syn_wa (.objEq z x) (syn_wex y (syn_wa (.objEq w y) ph))) x
  have p0031 :=
    @g_syl6 (.neg (.all y (.objEq y x)))
      (syn_wex y (syn_wa (syn_wa (.objEq z x) (.objEq w y)) ph))
      (syn_wa (.objEq z x) (syn_wex y (syn_wa (.objEq w y) ph)))
      (syn_wex x (syn_wa (.objEq z x) (syn_wex y (syn_wa (.objEq w y) ph)))) p0029 p0030
  have p0032 :=
    @g_pm2_61i (.all y (.objEq y x))
      (.imp (syn_wex y (syn_wa (syn_wa (.objEq z x) (.objEq w y)) ph))
        (syn_wex x (syn_wa (.objEq z x) (syn_wex y (syn_wa (.objEq w y) ph)))))
      p0020 p0031
  have p0033 :=
    @g_exlimi (syn_wex y (syn_wa (syn_wa (.objEq z x) (.objEq w y)) ph))
      (syn_wex x (syn_wa (.objEq z x) (syn_wex y (syn_wa (.objEq w y) ph)))) x p0010 p0032
  have p0034 := @g_euequ1 x z dv_cache_0009
  have p0035 := @g_equcom x z
  have p0036 := @g_eubii (.objEq x z) (.objEq z x) x p0035
  have p0037 := @g_mpbi (syn_weu x (.objEq x z)) (syn_weu x (.objEq z x)) p0034 p0036
  have p0038 := @g_eupick (.objEq z x) (syn_wex y (syn_wa (.objEq w y) ph)) x
  have p0039 :=
    @g_mpan (syn_weu x (.objEq z x))
      (syn_wex x (syn_wa (.objEq z x) (syn_wex y (syn_wa (.objEq w y) ph))))
      (.imp (.objEq z x) (syn_wex y (syn_wa (.objEq w y) ph))) p0037 p0038
  have p0040 :=
    @g_com12 (syn_wex x (syn_wa (.objEq z x) (syn_wex y (syn_wa (.objEq w y) ph))))
      (.objEq z x) (syn_wex y (syn_wa (.objEq w y) ph)) p0039
  have p0041 := @g_euequ1 y w dv_cache_0010
  have p0042 := @g_equcom y w
  have p0043 := @g_eubii (.objEq y w) (.objEq w y) y p0042
  have p0044 := @g_mpbi (syn_weu y (.objEq y w)) (syn_weu y (.objEq w y)) p0041 p0043
  have p0045 := @g_eupick (.objEq w y) ph y
  have p0046 :=
    @g_mpan (syn_weu y (.objEq w y)) (syn_wex y (syn_wa (.objEq w y) ph))
      (.imp (.objEq w y) ph) p0044 p0045
  have p0047 := @g_com12 (syn_wex y (syn_wa (.objEq w y) ph)) (.objEq w y) ph p0046
  have p0048 :=
    @g_sylan9 (.objEq z x)
      (syn_wex x (syn_wa (.objEq z x) (syn_wex y (syn_wa (.objEq w y) ph))))
      (syn_wex y (syn_wa (.objEq w y) ph)) (.objEq w y) ph p0040 p0047
  have p0049 :=
    @g_syl5 (syn_wex x (syn_wex y (syn_wa (syn_wa (.objEq z x) (.objEq w y)) ph)))
      (syn_wex x (syn_wa (.objEq z x) (syn_wex y (syn_wa (.objEq w y) ph))))
      (syn_wa (.objEq z x) (.objEq w y)) ph p0033 p0048
  have p0050 :=
    @g_syl5bi
      (syn_wex x (syn_wex y
          (syn_wa (.classEq (syn_cop (.cv z) (.cv w)) (syn_cop (.cv x) (.cv y))) ph)))
      (syn_wex x (syn_wex y (syn_wa (syn_wa (.objEq z x) (.objEq w y)) ph)))
      (syn_wa (.objEq z x) (.objEq w y)) ph p0009 p0049
  have p0051_e00_recanon :
    Nominal.NPrf
      (syn_wb (.classEq (syn_cop (.cv z) (.cv w)) (syn_cop (.cv x) (.cv y)))
        (syn_wa (.objEq z x) (.objEq w y))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex
          syn_cphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0007
  have p0051 :=
    @g_sylbi (.classEq (syn_cop (.cv z) (.cv w)) (syn_cop (.cv x) (.cv y)))
      (syn_wa (.objEq z x) (.objEq w y))
      (.imp (syn_wex x (syn_wex y
            (syn_wa (.classEq (syn_cop (.cv z) (.cv w)) (syn_cop (.cv x) (.cv y))) ph))) ph)
      p0051_e00_recanon p0050
  have p0052 :=
    @g_impbid (.classEq (syn_cop (.cv z) (.cv w)) (syn_cop (.cv x) (.cv y))) ph
      (syn_wex x (syn_wex y
          (syn_wa (.classEq (syn_cop (.cv z) (.cv w)) (syn_cop (.cv x) (.cv y))) ph)))
      p0006 p0051
  have p0053 := @g_eqeq1 A (syn_cop (.cv z) (.cv w)) (syn_cop (.cv x) (.cv y))
  have p0054 :=
    @g_anbi1d (.classEq A (syn_cop (.cv z) (.cv w)))
      (.classEq A (syn_cop (.cv x) (.cv y)))
      (.classEq (syn_cop (.cv z) (.cv w)) (syn_cop (.cv x) (.cv y))) ph p0053
  have p0055 :=
    @g_n_2exbidv (.classEq A (syn_cop (.cv z) (.cv w)))
      (syn_wa (.classEq A (syn_cop (.cv x) (.cv y))) ph)
      (syn_wa (.classEq (syn_cop (.cv z) (.cv w)) (syn_cop (.cv x) (.cv y))) ph) x y
      dv_cache_0011 dv_cache_0012 p0054
  have p0056 :=
    @g_bibi2d (.classEq A (syn_cop (.cv z) (.cv w)))
      (syn_wex x (syn_wex y (syn_wa (.classEq A (syn_cop (.cv x) (.cv y))) ph)))
      (syn_wex x (syn_wex y
          (syn_wa (.classEq (syn_cop (.cv z) (.cv w)) (syn_cop (.cv x) (.cv y))) ph)))
      ph p0055
  have p0057 :=
    @g_imbi12d (.classEq A (syn_cop (.cv z) (.cv w)))
      (.classEq A (syn_cop (.cv x) (.cv y)))
      (.classEq (syn_cop (.cv z) (.cv w)) (syn_cop (.cv x) (.cv y)))
      (syn_wb ph (syn_wex x (syn_wex y (syn_wa (.classEq A (syn_cop (.cv x) (.cv y))) ph))))
      (syn_wb ph (syn_wex x (syn_wex y
            (syn_wa (.classEq (syn_cop (.cv z) (.cv w)) (syn_cop (.cv x) (.cv y))) ph))))
      p0053 p0056
  have p0058 :=
    @g_mpbiri (.classEq A (syn_cop (.cv z) (.cv w)))
      (.imp (.classEq A (syn_cop (.cv x) (.cv y))) (syn_wb ph
          (syn_wex x (syn_wex y (syn_wa (.classEq A (syn_cop (.cv x) (.cv y))) ph)))))
      (.imp (.classEq (syn_cop (.cv z) (.cv w)) (syn_cop (.cv x) (.cv y))) (syn_wb ph (syn_wex x
            (syn_wex y (syn_wa (.classEq (syn_cop (.cv z) (.cv w)) (syn_cop (.cv x) (.cv y)))
                ph)))))
      p0052 p0057
  have p0059 :=
    @g_adantr (.classEq A (syn_cop (.cv z) (.cv w)))
      (.imp (.classEq A (syn_cop (.cv x) (.cv y))) (syn_wb ph
          (syn_wex x (syn_wex y (syn_wa (.classEq A (syn_cop (.cv x) (.cv y))) ph)))))
      (.classEq (syn_cop (.cv z) (.cv w)) (syn_cop (.cv x) (.cv y))) p0058
  have p0060 :=
    @g_exlimivv
      (syn_wa (.classEq A (syn_cop (.cv z) (.cv w)))
        (.classEq (syn_cop (.cv z) (.cv w)) (syn_cop (.cv x) (.cv y))))
      (.imp (.classEq A (syn_cop (.cv x) (.cv y))) (syn_wb ph
          (syn_wex x (syn_wex y (syn_wa (.classEq A (syn_cop (.cv x) (.cv y))) ph)))))
      z w dv_cache_0013 dv_cache_0014 p0059
  have p0061 :=
    @g_sylbi (.classEq A (syn_cop (.cv x) (.cv y)))
      (syn_wex z (syn_wex w (syn_wa (.classEq A (syn_cop (.cv z) (.cv w)))
            (.classEq (syn_cop (.cv z) (.cv w)) (syn_cop (.cv x) (.cv y))))))
      (.imp (.classEq A (syn_cop (.cv x) (.cv y))) (syn_wb ph
          (syn_wex x (syn_wex y (syn_wa (.classEq A (syn_cop (.cv x) (.cv y))) ph)))))
      p0002 p0060
  have p0062 :=
    @g_pm2_43i (.classEq A (syn_cop (.cv x) (.cv y)))
      (syn_wb ph (syn_wex x (syn_wex y (syn_wa (.classEq A (syn_cop (.cv x) (.cv y))) ph))))
      p0061
  exact p0062

@[expose]
noncomputable def g_copsex2g (ph : Wff) (ps : Wff) (x : Var) (y : Var) (A : Class)
    (B : Class) (V : Class) (W : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv)
    (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_ps_x : x ∉ ps.fv) (dv_ps_y : y ∉ ps.fv)
    (dv_x_y : x ≠ y)
    (hyp_copsex2g_1 : Nominal.NPrf
        (.imp (syn_wa (.classEq (.cv x) A) (.classEq (.cv y) B)) (syn_wb ph ps))) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A V) (.classMem B W)) (syn_wb (syn_wex x
            (syn_wex y (syn_wa (.classEq (syn_cop A B) (syn_cop (.cv x) (.cv y))) ph))) ps)) :=
  by
  have dv_cache_0001 : x ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have dv_cache_0002 : y ∉ (B).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_y, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((Wff.classEq (.cv x) A)).fv :=
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
          Finset.mem_singleton, (Ne.symm dv_x_y), dv_A_y, or_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((Wff.classEq (.cv y) B)).fv :=
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
          Finset.mem_singleton, dv_x_y, dv_B_x, or_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ (ps).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_ps_x, not_false_eq_true])
  have dv_cache_0006 : y ∉ (ps).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_ps_y, not_false_eq_true])
  have dv_cache_0007 : x ∉ ((syn_cop A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          dv_A_x, dv_B_x, or_false, not_false_eq_true])
  have dv_cache_0008 : y ∉ ((syn_cop A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          dv_A_y, dv_B_y, or_false, not_false_eq_true])
  have p0000 := @g_elisset x A V dv_cache_0001
  have p0001 := @g_elisset y B W dv_cache_0002
  have p0002 :=
    @g_eeanv (.classEq (.cv x) A) (.classEq (.cv y) B) x y dv_cache_0003 dv_cache_0004
  have p0003 :=
    @g_nfe1 (syn_wex y (syn_wa (.classEq (syn_cop A B) (syn_cop (.cv x) (.cv y))) ph)) x
  have p0004 := @g_nfv ps x dv_cache_0005
  have p0005 :=
    @g_nfbi
      (syn_wex x (syn_wex y (syn_wa (.classEq (syn_cop A B) (syn_cop (.cv x) (.cv y))) ph)))
      ps x p0003 p0004
  have p0006 := @g_nfe1 (syn_wa (.classEq (syn_cop A B) (syn_cop (.cv x) (.cv y))) ph) y
  have p0007 :=
    @g_nfex (syn_wex y (syn_wa (.classEq (syn_cop A B) (syn_cop (.cv x) (.cv y))) ph)) y x
      p0006
  have p0008 := @g_nfv ps y dv_cache_0006
  have p0009 :=
    @g_nfbi
      (syn_wex x (syn_wex y (syn_wa (.classEq (syn_cop A B) (syn_cop (.cv x) (.cv y))) ph)))
      ps y p0007 p0008
  have p0010 := @g_opeq12 (.cv x) A (.cv y) B
  have p0011 := @g_copsexg ph x y (syn_cop A B) dv_cache_0007 dv_cache_0008
  have p0012 :=
    @g_eqcoms
      (syn_wb ph (syn_wex x
          (syn_wex y (syn_wa (.classEq (syn_cop A B) (syn_cop (.cv x) (.cv y))) ph))))
      (syn_cop A B) (syn_cop (.cv x) (.cv y)) p0011
  have p0013 :=
    @g_syl (syn_wa (.classEq (.cv x) A) (.classEq (.cv y) B))
      (.classEq (syn_cop (.cv x) (.cv y)) (syn_cop A B))
      (syn_wb ph (syn_wex x
          (syn_wex y (syn_wa (.classEq (syn_cop A B) (syn_cop (.cv x) (.cv y))) ph))))
      p0010 p0012
  have p0014 :=
    @g_bitr3d (syn_wa (.classEq (.cv x) A) (.classEq (.cv y) B)) ph
      (syn_wex x (syn_wex y (syn_wa (.classEq (syn_cop A B) (syn_cop (.cv x) (.cv y))) ph)))
      ps p0013 hyp_copsex2g_1
  have p0015 :=
    @g_exlimi (syn_wa (.classEq (.cv x) A) (.classEq (.cv y) B))
      (syn_wb (syn_wex x
          (syn_wex y (syn_wa (.classEq (syn_cop A B) (syn_cop (.cv x) (.cv y))) ph))) ps)
      y p0009 p0014
  have p0016 :=
    @g_exlimi (syn_wex y (syn_wa (.classEq (.cv x) A) (.classEq (.cv y) B)))
      (syn_wb (syn_wex x
          (syn_wex y (syn_wa (.classEq (syn_cop A B) (syn_cop (.cv x) (.cv y))) ph))) ps)
      x p0005 p0015
  have p0017 :=
    @g_sylbir (syn_wa (syn_wex x (.classEq (.cv x) A)) (syn_wex y (.classEq (.cv y) B)))
      (syn_wex x (syn_wex y (syn_wa (.classEq (.cv x) A) (.classEq (.cv y) B))))
      (syn_wb (syn_wex x
          (syn_wex y (syn_wa (.classEq (syn_cop A B) (syn_cop (.cv x) (.cv y))) ph))) ps)
      p0002 p0016
  have p0018 :=
    @g_syl2an (.classMem A V) (syn_wex x (.classEq (.cv x) A))
      (syn_wex y (.classEq (.cv y) B))
      (syn_wb (syn_wex x
          (syn_wex y (syn_wa (.classEq (syn_cop A B) (syn_cop (.cv x) (.cv y))) ph))) ps)
      (.classMem B W) p0000 p0001 p0017
  exact p0018

@[expose]
noncomputable def g_eqop (z : Var) (t : Var) (A : Class) (B : Class) (C : Class)
    (_dv_A_t : t ∉ A.fv) (dv_A_z : z ∉ A.fv) (dv_B_t : t ∉ B.fv) (dv_B_z : z ∉ B.fv)
    (dv_C_t : t ∉ C.fv) (dv_C_z : z ∉ C.fv) (dv_t_z : t ≠ z) :
    Nominal.NPrf
      (syn_wb (.classEq A (syn_cop B C)) (.all z (syn_wb (.classMem (.cv z) A)
            (syn_wo (syn_wrex t B (.classEq (.cv z) (syn_cphi (.cv t)))) (syn_wrex t C
                (.classEq (.cv z) (syn_cun (syn_cphi (.cv t)) (syn_csn (syn_c0c))))))))) :=
  by
  have dv_cache_0001 : z ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_z, not_false_eq_true])
  have dv_cache_0002 : z ∉ ((syn_cop B C)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          dv_B_z, dv_C_z, or_false, not_false_eq_true])
  have dv_cache_0003 : z ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_z, not_false_eq_true])
  have dv_cache_0004 : t ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_t, not_false_eq_true])
  have dv_cache_0005 : z ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_z, not_false_eq_true])
  have dv_cache_0006 : t ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_t, not_false_eq_true])
  have dv_cache_0007 : z ≠ t :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show z ≠ t from (by exact Ne.symm dv_t_z))
  have p0000 := @g_dfcleq z A (syn_cop B C) dv_cache_0001 dv_cache_0002
  have p0001 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_op z t B C
      dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0002 :=
    @g_eleq2i (syn_cop B C)
      (syn_cun (.cab z (syn_wrex t B (.classEq (.cv z) (syn_cphi (.cv t))))) (.cab z
          (syn_wrex t C (.classEq (.cv z) (syn_cun (syn_cphi (.cv t)) (syn_csn (syn_c0c)))))))
      (.cv z) p0001
  have p0003 :=
    @g_elun (.cv z) (.cab z (syn_wrex t B (.classEq (.cv z) (syn_cphi (.cv t)))))
      (.cab z (syn_wrex t C
          (.classEq (.cv z) (syn_cun (syn_cphi (.cv t)) (syn_csn (syn_c0c))))))
  have p0004 :=
    @g_bitri (.classMem (.cv z) (syn_cop B C))
      (.classMem (.cv z) (syn_cun (.cab z (syn_wrex t B (.classEq (.cv z) (syn_cphi (.cv t)))))
          (.cab z (syn_wrex t C
              (.classEq (.cv z) (syn_cun (syn_cphi (.cv t)) (syn_csn (syn_c0c))))))))
      (syn_wo (.classMem (.cv z) (.cab z (syn_wrex t B (.classEq (.cv z) (syn_cphi (.cv t))))))
        (.classMem (.cv z) (.cab z (syn_wrex t C
              (.classEq (.cv z) (syn_cun (syn_cphi (.cv t)) (syn_csn (syn_c0c))))))))
      p0002 p0003
  have p0005 := @g_abid (syn_wrex t B (.classEq (.cv z) (syn_cphi (.cv t)))) z
  have p0006 :=
    @g_abid
      (syn_wrex t C (.classEq (.cv z) (syn_cun (syn_cphi (.cv t)) (syn_csn (syn_c0c))))) z
  have p0007 :=
    @g_orbi12i
      (.classMem (.cv z) (.cab z (syn_wrex t B (.classEq (.cv z) (syn_cphi (.cv t))))))
      (syn_wrex t B (.classEq (.cv z) (syn_cphi (.cv t))))
      (.classMem (.cv z) (.cab z (syn_wrex t C
            (.classEq (.cv z) (syn_cun (syn_cphi (.cv t)) (syn_csn (syn_c0c)))))))
      (syn_wrex t C (.classEq (.cv z) (syn_cun (syn_cphi (.cv t)) (syn_csn (syn_c0c)))))
      p0005 p0006
  have p0008 :=
    @g_bitri (.classMem (.cv z) (syn_cop B C))
      (syn_wo (.classMem (.cv z) (.cab z (syn_wrex t B (.classEq (.cv z) (syn_cphi (.cv t))))))
        (.classMem (.cv z) (.cab z (syn_wrex t C
              (.classEq (.cv z) (syn_cun (syn_cphi (.cv t)) (syn_csn (syn_c0c))))))))
      (syn_wo (syn_wrex t B (.classEq (.cv z) (syn_cphi (.cv t)))) (syn_wrex t C
          (.classEq (.cv z) (syn_cun (syn_cphi (.cv t)) (syn_csn (syn_c0c))))))
      p0004 p0007
  have p0009 :=
    @g_bibi2i (.classMem (.cv z) (syn_cop B C))
      (syn_wo (syn_wrex t B (.classEq (.cv z) (syn_cphi (.cv t)))) (syn_wrex t C
          (.classEq (.cv z) (syn_cun (syn_cphi (.cv t)) (syn_csn (syn_c0c))))))
      (.classMem (.cv z) A) p0008
  have p0010 :=
    @g_albii (syn_wb (.classMem (.cv z) A) (.classMem (.cv z) (syn_cop B C)))
      (syn_wb (.classMem (.cv z) A) (syn_wo (syn_wrex t B (.classEq (.cv z) (syn_cphi (.cv t))))
          (syn_wrex t C (.classEq (.cv z) (syn_cun (syn_cphi (.cv t)) (syn_csn (syn_c0c)))))))
      z p0009
  have p0011 :=
    @g_bitri (.classEq A (syn_cop B C))
      (.all z (syn_wb (.classMem (.cv z) A) (.classMem (.cv z) (syn_cop B C))))
      (.all z (syn_wb (.classMem (.cv z) A)
          (syn_wo (syn_wrex t B (.classEq (.cv z) (syn_cphi (.cv t)))) (syn_wrex t C
              (.classEq (.cv z) (syn_cun (syn_cphi (.cv t)) (syn_csn (syn_c0c))))))))
      p0000 p0010
  exact p0011

@[expose]
noncomputable def g_mosubopt (ph : Wff) (x : Var) (y : Var) (z : Var) (A : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv) (dv_x_y : x ≠ y)
    (dv_x_z : x ≠ z) (_dv_y_z : y ≠ z) :
    Nominal.NPrf
      (.imp (.all y (.all z (syn_wmo x ph))) (syn_wmo x
          (syn_wex y (syn_wex z (syn_wa (.classEq A (syn_cop (.cv y) (.cv z))) ph))))) :=
  by
  have dv_cache_0001 : y ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_y, not_false_eq_true])
  have dv_cache_0002 : z ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_z, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((Wff.classEq A (syn_cop (.cv y) (.cv z)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_A_x, dv_x_y, dv_x_z, or_false, not_false_eq_true])
  have dv_cache_0004 :
    x ∉ ((syn_wex y (syn_wex z (.classEq A (syn_cop (.cv y) (.cv z)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, dv_A_x, dv_x_y, dv_x_z, or_false, and_false,
          not_false_eq_true])
  have p0000 := @g_nfa1 (.all z (syn_wmo x ph)) y
  have p0001 := @g_nfe1 (syn_wex z (syn_wa (.classEq A (syn_cop (.cv y) (.cv z))) ph)) y
  have p0002 :=
    @g_nfmo (syn_wex y (syn_wex z (syn_wa (.classEq A (syn_cop (.cv y) (.cv z))) ph))) y x
      p0001
  have p0003 := @g_nfa1 (syn_wmo x ph) z
  have p0004 := @g_nfe1 (syn_wa (.classEq A (syn_cop (.cv y) (.cv z))) ph) z
  have p0005 :=
    @g_nfex (syn_wex z (syn_wa (.classEq A (syn_cop (.cv y) (.cv z))) ph)) z y p0004
  have p0006 :=
    @g_nfmo (syn_wex y (syn_wex z (syn_wa (.classEq A (syn_cop (.cv y) (.cv z))) ph))) z x
      p0005
  have p0007 := @g_copsexg ph y z A dv_cache_0001 dv_cache_0002
  have p0008 :=
    @g_mobidv (.classEq A (syn_cop (.cv y) (.cv z))) ph
      (syn_wex y (syn_wex z (syn_wa (.classEq A (syn_cop (.cv y) (.cv z))) ph))) x
      dv_cache_0003 p0007
  have p0009 :=
    @g_biimpcd (.classEq A (syn_cop (.cv y) (.cv z))) (syn_wmo x ph)
      (syn_wmo x (syn_wex y (syn_wex z (syn_wa (.classEq A (syn_cop (.cv y) (.cv z))) ph))))
      p0008
  have p0010 :=
    @g_sps (syn_wmo x ph)
      (.imp (.classEq A (syn_cop (.cv y) (.cv z))) (syn_wmo x
          (syn_wex y (syn_wex z (syn_wa (.classEq A (syn_cop (.cv y) (.cv z))) ph)))))
      z p0009
  have p0011 :=
    @g_exlimd (.all z (syn_wmo x ph)) (.classEq A (syn_cop (.cv y) (.cv z)))
      (syn_wmo x (syn_wex y (syn_wex z (syn_wa (.classEq A (syn_cop (.cv y) (.cv z))) ph))))
      z p0003 p0006 p0010
  have p0012 :=
    @g_sps (.all z (syn_wmo x ph))
      (.imp (syn_wex z (.classEq A (syn_cop (.cv y) (.cv z)))) (syn_wmo x
          (syn_wex y (syn_wex z (syn_wa (.classEq A (syn_cop (.cv y) (.cv z))) ph)))))
      y p0011
  have p0013 :=
    @g_exlimd (.all y (.all z (syn_wmo x ph)))
      (syn_wex z (.classEq A (syn_cop (.cv y) (.cv z))))
      (syn_wmo x (syn_wex y (syn_wex z (syn_wa (.classEq A (syn_cop (.cv y) (.cv z))) ph))))
      y p0000 p0002 p0012
  have p0014 := @g_simpl (.classEq A (syn_cop (.cv y) (.cv z))) ph
  have p0015 :=
    @g_n_2eximi (syn_wa (.classEq A (syn_cop (.cv y) (.cv z))) ph)
      (.classEq A (syn_cop (.cv y) (.cv z))) y z p0014
  have p0016 :=
    @g_exlimiv (syn_wex y (syn_wex z (syn_wa (.classEq A (syn_cop (.cv y) (.cv z))) ph)))
      (syn_wex y (syn_wex z (.classEq A (syn_cop (.cv y) (.cv z))))) x dv_cache_0004 p0015
  have p0017 :=
    @g_con3i
      (syn_wex x (syn_wex y (syn_wex z (syn_wa (.classEq A (syn_cop (.cv y) (.cv z))) ph))))
      (syn_wex y (syn_wex z (.classEq A (syn_cop (.cv y) (.cv z))))) p0016
  have p0018 :=
    @g_exmo (syn_wex y (syn_wex z (syn_wa (.classEq A (syn_cop (.cv y) (.cv z))) ph))) x
  have p0019 :=
    @g_ori
      (syn_wex x (syn_wex y (syn_wex z (syn_wa (.classEq A (syn_cop (.cv y) (.cv z))) ph))))
      (syn_wmo x (syn_wex y (syn_wex z (syn_wa (.classEq A (syn_cop (.cv y) (.cv z))) ph))))
      p0018
  have p0020 :=
    @g_syl (.neg (syn_wex y (syn_wex z (.classEq A (syn_cop (.cv y) (.cv z))))))
      (.neg (syn_wex x
          (syn_wex y (syn_wex z (syn_wa (.classEq A (syn_cop (.cv y) (.cv z))) ph)))))
      (syn_wmo x (syn_wex y (syn_wex z (syn_wa (.classEq A (syn_cop (.cv y) (.cv z))) ph))))
      p0017 p0019
  have p0021 :=
    @g_pm2_61d1 (.all y (.all z (syn_wmo x ph)))
      (syn_wex y (syn_wex z (.classEq A (syn_cop (.cv y) (.cv z)))))
      (syn_wmo x (syn_wex y (syn_wex z (syn_wa (.classEq A (syn_cop (.cv y) (.cv z))) ph))))
      p0013 p0020
  exact p0021


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk010Compact001Part036`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_phiun (A : Class) (B : Class) :
    Nominal.NPrf
      (.classEq (syn_cphi (syn_cun A B)) (syn_cun (syn_cphi A) (syn_cphi B))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have dv_cache_0001 : y ∉ ((syn_cun A B)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
          fresh_y_not_A, fresh_y_not_B, or_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((syn_cun A B)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true])
  have dv_cache_0003 : y ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show y ≠ x from (by exact fresh_y_ne_x))
  have dv_cache_0004 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0005 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0006 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_B, not_false_eq_true])
  have dv_cache_0007 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_B, not_false_eq_true])
  have p0000 :=
    @g_rexun
      (.classEq (.cv x)
        (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)))
      y A B
  have p0001 :=
    @g_abbii
      (syn_wrex y (syn_cun A B) (.classEq (.cv x)
          (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))))
      (syn_wo (syn_wrex y A (.classEq (.cv x)
            (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))))
        (syn_wrex y B (.classEq (.cv x)
            (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)))))
      x p0000
  have p0002 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_phi y x
      (syn_cun A B) dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0003 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_phi y x A
      dv_cache_0004 dv_cache_0005 dv_cache_0003
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_phi y x B
      dv_cache_0006 dv_cache_0007 dv_cache_0003
  have p0005 :=
    @g_uneq12i (syn_cphi A)
      (.cab x (syn_wrex y A (.classEq (.cv x)
            (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)))))
      (syn_cphi B)
      (.cab x (syn_wrex y B (.classEq (.cv x)
            (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)))))
      p0003 p0004
  have p0006 :=
    @g_unab
      (syn_wrex y A (.classEq (.cv x)
          (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))))
      (syn_wrex y B (.classEq (.cv x)
          (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))))
      x
  have p0007 :=
    @g_eqtri (syn_cun (syn_cphi A) (syn_cphi B))
      (syn_cun (.cab x (syn_wrex y A (.classEq (.cv x)
              (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)))))
        (.cab x (syn_wrex y B (.classEq (.cv x)
              (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))))))
      (.cab x (syn_wo (syn_wrex y A (.classEq (.cv x)
              (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))))
          (syn_wrex y B (.classEq (.cv x)
              (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))))))
      p0005 p0006
  have p0008 :=
    @g_n_3eqtr4i
      (.cab x (syn_wrex y (syn_cun A B) (.classEq (.cv x)
            (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)))))
      (.cab x (syn_wo (syn_wrex y A (.classEq (.cv x)
              (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))))
          (syn_wrex y B (.classEq (.cv x)
              (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))))))
      (syn_cphi (syn_cun A B)) (syn_cun (syn_cphi A) (syn_cphi B)) p0001 p0002 p0007
  exact p0008

@[expose]
noncomputable def g_phidisjnn (A : Class) :
    Nominal.NPrf
      (.imp (.classEq (syn_cin A (syn_cnnc)) (syn_c0)) (.classEq (syn_cphi A) A)) :=
  by
  let proofSupport : Finset Var := A.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (h)
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have dv_cache_0001 : y ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_cnnc)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((Wff.classEq (syn_cin A (syn_cnnc)) (syn_c0))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          fresh_y_not_A, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_x, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((Wff.classEq (syn_cin A (syn_cnnc)) (syn_c0))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          fresh_x_not_A, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0006 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0007 : y ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show y ≠ x from (by exact fresh_y_ne_x))
  have p0000 := @g_disj y A (syn_cnnc) dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_biimpi (.classEq (syn_cin A (syn_cnnc)) (syn_c0))
      (syn_wral y A (.neg (.classMem (.cv y) (syn_cnnc)))) p0000
  have p0002 :=
    @g_r19_21bi (.classEq (syn_cin A (syn_cnnc)) (syn_c0))
      (.neg (.classMem (.cv y) (syn_cnnc))) y A p0001
  have p0003 :=
    @g_iffalse (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)
  have p0004 :=
    @g_syl (syn_wa (.classEq (syn_cin A (syn_cnnc)) (syn_c0)) (.classMem (.cv y) A))
      (.neg (.classMem (.cv y) (syn_cnnc)))
      (.classEq (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))
        (.cv y))
      p0002 p0003
  have p0005 :=
    @g_eqeq2d (syn_wa (.classEq (syn_cin A (syn_cnnc)) (syn_c0)) (.classMem (.cv y) A))
      (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))
      (.cv y) (.cv x) p0004
  have p0006 := @g_equcom y x
  have p0007_e00_recanon :
    Nominal.NPrf
      (.imp (syn_wa (.classEq (syn_cin A (syn_cnnc)) (syn_c0)) (.classMem (.cv y) A)) (syn_wb
          (.classEq (.cv x)
            (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)))
          (.objEq x y))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_cin syn_ccompl syn_cnin syn_wnan syn_cnnc syn_cint syn_c0
          syn_cdif syn_cvv syn_wb syn_cif syn_wo syn_cplc syn_wrex syn_wex syn_c1c
        simp (config :=
          {
            failIfUnchanged :=
              false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0005
  have p0007 :=
    @g_syl6bbr (syn_wa (.classEq (syn_cin A (syn_cnnc)) (syn_c0)) (.classMem (.cv y) A))
      (.classEq (.cv x)
        (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)))
      (.objEq x y) (.objEq y x) p0007_e00_recanon p0006
  have p0008 :=
    @g_rexbidva (.classEq (syn_cin A (syn_cnnc)) (syn_c0))
      (.classEq (.cv x)
        (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)))
      (.objEq y x) y A dv_cache_0003 p0007
  have p0009 := @g_risset y (.cv x) A dv_cache_0004 dv_cache_0001
  have p0010_e01_recanon :
    Nominal.NPrf (syn_wb (.classMem (.cv x) A) (syn_wrex y A (.objEq y x))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb, syn_wrex, syn_wex, syn_wa]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0009
  have p0010 :=
    @g_syl6bbr (.classEq (syn_cin A (syn_cnnc)) (syn_c0))
      (syn_wrex y A (.classEq (.cv x)
          (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))))
      (syn_wrex y A (.objEq y x)) (.classMem (.cv x) A) p0008 p0010_e01_recanon
  have p0011 :=
    @g_alrimiv (.classEq (syn_cin A (syn_cnnc)) (syn_c0))
      (syn_wb (syn_wrex y A (.classEq (.cv x)
            (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))))
        (.classMem (.cv x) A))
      x dv_cache_0005 p0010
  have p0012 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_phi y x A
      dv_cache_0001 dv_cache_0006 dv_cache_0007
  have p0013 :=
    @g_eqeq1i (syn_cphi A)
      (.cab x (syn_wrex y A (.classEq (.cv x)
            (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)))))
      A p0012
  have p0014 :=
    @g_eqabcb
      (syn_wrex y A (.classEq (.cv x)
          (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))))
      x A dv_cache_0006
  have p0015 :=
    @g_bitri (.classEq (syn_cphi A) A)
      (.classEq (.cab x (syn_wrex y A (.classEq (.cv x)
              (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)))))
        A)
      (.all x (syn_wb (syn_wrex y A (.classEq (.cv x)
              (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))))
          (.classMem (.cv x) A)))
      p0013 p0014
  have p0016 :=
    @g_sylibr (.classEq (syn_cin A (syn_cnnc)) (syn_c0))
      (.all x (syn_wb (syn_wrex y A (.classEq (.cv x)
              (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))))
          (.classMem (.cv x) A)))
      (.classEq (syn_cphi A) A) p0011 p0015
  exact p0016


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk010Compact001Part037`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_phialllem1 (x : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (hyp_phiall_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wss A (syn_cnnc)) (.neg (.classMem (syn_c0c) A)))
        (syn_wex x (.classEq A (syn_cphi (.cv x))))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv
  let z : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let w : Var := freshVar proofSupport 2
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_w : x ≠ w := Ne.symm fresh_w_ne_x
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have fresh_z_ne_y : z ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_z : y ≠ z := Ne.symm fresh_z_ne_y
  have fresh_z_ne_w : z ≠ w :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_w_ne_z : w ≠ z := Ne.symm fresh_z_ne_w
  have fresh_y_ne_w : y ≠ w :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_w_ne_y : w ≠ y := Ne.symm fresh_y_ne_w
  have dv_cache_0001 : x ∉ ((Class.cv z)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_z, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((Wff.objEq z w)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
          Finset.mem_singleton, fresh_x_ne_z, fresh_x_ne_w, or_false, not_false_eq_true])
  have dv_cache_0003 :
    z ∉ ((syn_wa (syn_wss A (syn_cnnc)) (.neg (.classMem (syn_c0c) A)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
          fresh_z_not_A, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0004 : z ∉ ((Class.cv w)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_w, not_false_eq_true])
  have dv_cache_0005 : z ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_A, not_false_eq_true])
  have dv_cache_0006 : z ∉ ((syn_cnnc)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0007 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have dv_cache_0008 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0009 : w ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_A, not_false_eq_true])
  have dv_cache_0010 :
    w ∉ ((syn_wa (syn_wss A (syn_cnnc)) (.neg (.classMem (syn_c0c) A)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
          fresh_w_not_A, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0011 :
    x ∉
      ((syn_crab y (syn_cnnc)
          (syn_wrex z A (.classEq (.cv z) (syn_cplc (.cv y) (syn_c1c)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, dv_A_x, fresh_x_ne_z, fresh_x_ne_y,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0012 :
    w ∉
      ((syn_crab y (syn_cnnc)
          (syn_wrex z A (.classEq (.cv z) (syn_cplc (.cv y) (syn_c1c)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_w_not_A, fresh_w_ne_z,
          fresh_w_ne_y, compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0013 : x ≠ w :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact (show x ≠ w from (by exact fresh_x_ne_w))
  have dv_cache_0014 : z ∉ ((Wff.objEq y x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
          Finset.mem_singleton, fresh_z_ne_y, fresh_z_ne_x, or_false, not_false_eq_true])
  have dv_cache_0015 : y ∉ ((syn_cnnc)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0016 :
    y ∉ ((syn_wrex z A (.classEq (.cv z) (syn_cplc (.cv x) (syn_c1c))))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_y_not_A, fresh_y_ne_z,
          fresh_y_ne_x, compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0017 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0018 : z ∉ ((Wff.classEq (.cv w) (syn_cplc (.cv x) (syn_c1c)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_w, fresh_z_ne_x, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0019 :
    z ∉
      ((syn_ccnvk (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                      (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                  (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                    (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                      (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
              (syn_cpw1 (syn_cpw1 (syn_c1c))))))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimagek,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0020 : z ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_y, not_false_eq_true])
  have dv_cache_0021 :
    y ∉
      ((syn_cimak (syn_ccnvk (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                      (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                    (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                      (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                        (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                (syn_cpw1 (syn_cpw1 (syn_c1c)))))) A)).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimagek,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik, Finset.mem_union,
          fresh_y_not_A, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0022 :
    x ∉
      ((Wff.classEq A (syn_cphi (syn_crab y (syn_cnnc)
              (syn_wrex z A (.classEq (.cv z) (syn_cplc (.cv y) (syn_c1c)))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cphi,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, dv_A_x, fresh_x_ne_z, fresh_x_ne_y,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have p0000 := @g_eleq1 (.cv z) (syn_c0c) A
  have p0001 :=
    @g_biimpcd (.classEq (.cv z) (syn_c0c)) (.classMem (.cv z) A) (.classMem (syn_c0c) A)
      p0000
  have p0002 :=
    @g_con3d (.classMem (.cv z) A) (.classEq (.cv z) (syn_c0c)) (.classMem (syn_c0c) A)
      p0001
  have p0003 :=
    @g_impcom (.classMem (.cv z) A) (.neg (.classMem (syn_c0c) A))
      (.neg (.classEq (.cv z) (syn_c0c))) p0002
  have p0004 :=
    @g_adantll (.neg (.classMem (syn_c0c) A)) (.classMem (.cv z) A)
      (.neg (.classEq (.cv z) (syn_c0c))) (syn_wss A (syn_cnnc)) p0003
  have p0005 := @g_ssel2 A (syn_cnnc) (.cv z)
  have p0006 :=
    @g_adantlr (syn_wss A (syn_cnnc)) (.classMem (.cv z) A) (.classMem (.cv z) (syn_cnnc))
      (.neg (.classMem (syn_c0c) A)) p0005
  have p0007 := @g_nnc0suc x (.cv z) dv_cache_0001
  have p0008 :=
    @g_sylib
      (syn_wa (syn_wa (syn_wss A (syn_cnnc)) (.neg (.classMem (syn_c0c) A)))
        (.classMem (.cv z) A))
      (.classMem (.cv z) (syn_cnnc))
      (syn_wo (.classEq (.cv z) (syn_c0c))
        (syn_wrex x (syn_cnnc) (.classEq (.cv z) (syn_cplc (.cv x) (syn_c1c)))))
      p0006 p0007
  have p0009 :=
    @g_orel1 (.classEq (.cv z) (syn_c0c))
      (syn_wrex x (syn_cnnc) (.classEq (.cv z) (syn_cplc (.cv x) (syn_c1c))))
  have p0010 :=
    @g_sylc
      (syn_wa (syn_wa (syn_wss A (syn_cnnc)) (.neg (.classMem (syn_c0c) A)))
        (.classMem (.cv z) A))
      (.neg (.classEq (.cv z) (syn_c0c)))
      (syn_wo (.classEq (.cv z) (syn_c0c))
        (syn_wrex x (syn_cnnc) (.classEq (.cv z) (syn_cplc (.cv x) (syn_c1c)))))
      (syn_wrex x (syn_cnnc) (.classEq (.cv z) (syn_cplc (.cv x) (syn_c1c)))) p0004 p0008
      p0009
  have p0011 := @g_anidm (.classEq (.cv z) (syn_cplc (.cv x) (syn_c1c)))
  have p0012 := @g_eqeq1 (.cv z) (.cv w) (syn_cplc (.cv x) (syn_c1c))
  have p0013_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq z w) (syn_wb (.classEq (.cv z) (syn_cplc (.cv x) (syn_c1c)))
          (.classEq (.cv w) (syn_cplc (.cv x) (syn_c1c))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cplc syn_wrex syn_wex syn_wa syn_c1c
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0012
  have p0013 :=
    @g_anbi2d (.objEq z w) (.classEq (.cv z) (syn_cplc (.cv x) (syn_c1c)))
      (.classEq (.cv w) (syn_cplc (.cv x) (syn_c1c)))
      (.classEq (.cv z) (syn_cplc (.cv x) (syn_c1c))) p0013_e00_recanon
  have p0014 :=
    @g_syl5bbr (.classEq (.cv z) (syn_cplc (.cv x) (syn_c1c)))
      (syn_wa (.classEq (.cv z) (syn_cplc (.cv x) (syn_c1c)))
        (.classEq (.cv z) (syn_cplc (.cv x) (syn_c1c))))
      (.objEq z w)
      (syn_wa (.classEq (.cv z) (syn_cplc (.cv x) (syn_c1c)))
        (.classEq (.cv w) (syn_cplc (.cv x) (syn_c1c))))
      p0011 p0013
  have p0015 :=
    @g_rexbidv (.objEq z w) (.classEq (.cv z) (syn_cplc (.cv x) (syn_c1c)))
      (syn_wa (.classEq (.cv z) (syn_cplc (.cv x) (syn_c1c)))
        (.classEq (.cv w) (syn_cplc (.cv x) (syn_c1c))))
      x (syn_cnnc) dv_cache_0002 p0014
  have p0016 :=
    @g_syl5ibcom
      (syn_wa (syn_wa (syn_wss A (syn_cnnc)) (.neg (.classMem (syn_c0c) A)))
        (.classMem (.cv z) A))
      (syn_wrex x (syn_cnnc) (.classEq (.cv z) (syn_cplc (.cv x) (syn_c1c)))) (.objEq z w)
      (syn_wrex x (syn_cnnc) (syn_wa (.classEq (.cv z) (syn_cplc (.cv x) (syn_c1c)))
          (.classEq (.cv w) (syn_cplc (.cv x) (syn_c1c)))))
      p0010 p0015
  have p0017 := @g_eqtr3 (.cv z) (.cv w) (syn_cplc (.cv x) (syn_c1c))
  have p0018_e00_recanon :
    Nominal.NPrf
      (.imp (syn_wa (.classEq (.cv z) (syn_cplc (.cv x) (syn_c1c)))
          (.classEq (.cv w) (syn_cplc (.cv x) (syn_c1c)))) (.objEq z w)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_cplc syn_wrex syn_wex syn_c1c
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0017
  have p0018 :=
    @g_rexlimivw
      (syn_wa (.classEq (.cv z) (syn_cplc (.cv x) (syn_c1c)))
        (.classEq (.cv w) (syn_cplc (.cv x) (syn_c1c))))
      (.objEq z w) x (syn_cnnc) dv_cache_0002 p0018_e00_recanon
  have p0019 :=
    @g_impbid1
      (syn_wa (syn_wa (syn_wss A (syn_cnnc)) (.neg (.classMem (syn_c0c) A)))
        (.classMem (.cv z) A))
      (.objEq z w)
      (syn_wrex x (syn_cnnc) (syn_wa (.classEq (.cv z) (syn_cplc (.cv x) (syn_c1c)))
          (.classEq (.cv w) (syn_cplc (.cv x) (syn_c1c)))))
      p0016 p0018
  have p0020 :=
    @g_rexbidva (syn_wa (syn_wss A (syn_cnnc)) (.neg (.classMem (syn_c0c) A)))
      (.objEq z w)
      (syn_wrex x (syn_cnnc) (syn_wa (.classEq (.cv z) (syn_cplc (.cv x) (syn_c1c)))
          (.classEq (.cv w) (syn_cplc (.cv x) (syn_c1c)))))
      z A dv_cache_0003 p0019
  have p0021 := @g_risset z (.cv w) A dv_cache_0004 dv_cache_0005
  have p0022 :=
    @g_rexcom
      (syn_wa (.classEq (.cv z) (syn_cplc (.cv x) (syn_c1c)))
        (.classEq (.cv w) (syn_cplc (.cv x) (syn_c1c))))
      x z (syn_cnnc) A dv_cache_0006 dv_cache_0007 dv_cache_0008
  have p0023_e01_recanon :
    Nominal.NPrf (syn_wb (.classMem (.cv w) A) (syn_wrex z A (.objEq z w))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb, syn_wrex, syn_wex, syn_wa]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0021
  have p0023 :=
    @g_n_3bitr4g (syn_wa (syn_wss A (syn_cnnc)) (.neg (.classMem (syn_c0c) A)))
      (syn_wrex z A (.objEq z w))
      (syn_wrex z A (syn_wrex x (syn_cnnc)
          (syn_wa (.classEq (.cv z) (syn_cplc (.cv x) (syn_c1c)))
            (.classEq (.cv w) (syn_cplc (.cv x) (syn_c1c))))))
      (.classMem (.cv w) A)
      (syn_wrex x (syn_cnnc) (syn_wrex z A
          (syn_wa (.classEq (.cv z) (syn_cplc (.cv x) (syn_c1c)))
            (.classEq (.cv w) (syn_cplc (.cv x) (syn_c1c))))))
      p0020 p0023_e01_recanon p0022
  have p0024 :=
    @g_eqabdv (syn_wa (syn_wss A (syn_cnnc)) (.neg (.classMem (syn_c0c) A)))
      (syn_wrex x (syn_cnnc) (syn_wrex z A
          (syn_wa (.classEq (.cv z) (syn_cplc (.cv x) (syn_c1c)))
            (.classEq (.cv w) (syn_cplc (.cv x) (syn_c1c))))))
      w A dv_cache_0009 dv_cache_0010 p0023
  have p0025 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_phi x w
      (syn_crab y (syn_cnnc) (syn_wrex z A (.classEq (.cv z) (syn_cplc (.cv y) (syn_c1c)))))
      dv_cache_0011 dv_cache_0012 dv_cache_0013
  have p0026 := @g_addceq1 (.cv y) (.cv x) (syn_c1c)
  have p0027_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq y x)
        (.classEq (syn_cplc (.cv y) (syn_c1c)) (syn_cplc (.cv x) (syn_c1c)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cplc syn_wrex syn_wex syn_wa syn_c1c
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0026
  have p0027 :=
    @g_eqeq2d (.objEq y x) (syn_cplc (.cv y) (syn_c1c)) (syn_cplc (.cv x) (syn_c1c))
      (.cv z) p0027_e00_recanon
  have p0028 :=
    @g_rexbidv (.objEq y x) (.classEq (.cv z) (syn_cplc (.cv y) (syn_c1c)))
      (.classEq (.cv z) (syn_cplc (.cv x) (syn_c1c))) z A dv_cache_0014 p0027
  have p0029 :=
    @g_rexrab (syn_wrex z A (.classEq (.cv z) (syn_cplc (.cv y) (syn_c1c))))
      (syn_wrex z A (.classEq (.cv z) (syn_cplc (.cv x) (syn_c1c))))
      (.classEq (.cv w)
        (syn_cif (.classMem (.cv x) (syn_cnnc)) (syn_cplc (.cv x) (syn_c1c)) (.cv x)))
      x y (syn_cnnc) dv_cache_0015 dv_cache_0016 dv_cache_0017 p0028
  have p0030 :=
    @g_iftrue (.classMem (.cv x) (syn_cnnc)) (syn_cplc (.cv x) (syn_c1c)) (.cv x)
  have p0031 :=
    @g_eqeq2d (.classMem (.cv x) (syn_cnnc))
      (syn_cif (.classMem (.cv x) (syn_cnnc)) (syn_cplc (.cv x) (syn_c1c)) (.cv x))
      (syn_cplc (.cv x) (syn_c1c)) (.cv w) p0030
  have p0032 :=
    @g_anbi2d (.classMem (.cv x) (syn_cnnc))
      (.classEq (.cv w)
        (syn_cif (.classMem (.cv x) (syn_cnnc)) (syn_cplc (.cv x) (syn_c1c)) (.cv x)))
      (.classEq (.cv w) (syn_cplc (.cv x) (syn_c1c)))
      (syn_wrex z A (.classEq (.cv z) (syn_cplc (.cv x) (syn_c1c)))) p0031
  have p0033 :=
    @g_r19_41v (.classEq (.cv z) (syn_cplc (.cv x) (syn_c1c)))
      (.classEq (.cv w) (syn_cplc (.cv x) (syn_c1c))) z A dv_cache_0018
  have p0034 :=
    @g_syl6bbr (.classMem (.cv x) (syn_cnnc))
      (syn_wa (syn_wrex z A (.classEq (.cv z) (syn_cplc (.cv x) (syn_c1c)))) (.classEq (.cv w)
          (syn_cif (.classMem (.cv x) (syn_cnnc)) (syn_cplc (.cv x) (syn_c1c)) (.cv x))))
      (syn_wa (syn_wrex z A (.classEq (.cv z) (syn_cplc (.cv x) (syn_c1c))))
        (.classEq (.cv w) (syn_cplc (.cv x) (syn_c1c))))
      (syn_wrex z A (syn_wa (.classEq (.cv z) (syn_cplc (.cv x) (syn_c1c)))
          (.classEq (.cv w) (syn_cplc (.cv x) (syn_c1c)))))
      p0032 p0033
  have p0035 :=
    @g_rexbiia
      (syn_wa (syn_wrex z A (.classEq (.cv z) (syn_cplc (.cv x) (syn_c1c)))) (.classEq (.cv w)
          (syn_cif (.classMem (.cv x) (syn_cnnc)) (syn_cplc (.cv x) (syn_c1c)) (.cv x))))
      (syn_wrex z A (syn_wa (.classEq (.cv z) (syn_cplc (.cv x) (syn_c1c)))
          (.classEq (.cv w) (syn_cplc (.cv x) (syn_c1c)))))
      x (syn_cnnc) p0034
  have p0036 :=
    @g_bitri
      (syn_wrex x (syn_crab y (syn_cnnc)
          (syn_wrex z A (.classEq (.cv z) (syn_cplc (.cv y) (syn_c1c))))) (.classEq (.cv w)
          (syn_cif (.classMem (.cv x) (syn_cnnc)) (syn_cplc (.cv x) (syn_c1c)) (.cv x))))
      (syn_wrex x (syn_cnnc)
        (syn_wa (syn_wrex z A (.classEq (.cv z) (syn_cplc (.cv x) (syn_c1c)))) (.classEq (.cv w)
            (syn_cif (.classMem (.cv x) (syn_cnnc)) (syn_cplc (.cv x) (syn_c1c)) (.cv x)))))
      (syn_wrex x (syn_cnnc) (syn_wrex z A
          (syn_wa (.classEq (.cv z) (syn_cplc (.cv x) (syn_c1c)))
            (.classEq (.cv w) (syn_cplc (.cv x) (syn_c1c))))))
      p0029 p0035
  have p0037 :=
    @g_abbii
      (syn_wrex x (syn_crab y (syn_cnnc)
          (syn_wrex z A (.classEq (.cv z) (syn_cplc (.cv y) (syn_c1c))))) (.classEq (.cv w)
          (syn_cif (.classMem (.cv x) (syn_cnnc)) (syn_cplc (.cv x) (syn_c1c)) (.cv x))))
      (syn_wrex x (syn_cnnc) (syn_wrex z A
          (syn_wa (.classEq (.cv z) (syn_cplc (.cv x) (syn_c1c)))
            (.classEq (.cv w) (syn_cplc (.cv x) (syn_c1c))))))
      w p0036
  have p0038 :=
    @g_eqtri
      (syn_cphi (syn_crab y (syn_cnnc)
          (syn_wrex z A (.classEq (.cv z) (syn_cplc (.cv y) (syn_c1c))))))
      (.cab w (syn_wrex x (syn_crab y (syn_cnnc)
            (syn_wrex z A (.classEq (.cv z) (syn_cplc (.cv y) (syn_c1c))))) (.classEq (.cv w)
            (syn_cif (.classMem (.cv x) (syn_cnnc)) (syn_cplc (.cv x) (syn_c1c)) (.cv x)))))
      (.cab w (syn_wrex x (syn_cnnc) (syn_wrex z A
            (syn_wa (.classEq (.cv z) (syn_cplc (.cv x) (syn_c1c)))
              (.classEq (.cv w) (syn_cplc (.cv x) (syn_c1c)))))))
      p0025 p0037
  have p0039 :=
    @g_syl6eqr (syn_wa (syn_wss A (syn_cnnc)) (.neg (.classMem (syn_c0c) A))) A
      (.cab w (syn_wrex x (syn_cnnc) (syn_wrex z A
            (syn_wa (.classEq (.cv z) (syn_cplc (.cv x) (syn_c1c)))
              (.classEq (.cv w) (syn_cplc (.cv x) (syn_c1c)))))))
      (syn_cphi (syn_crab y (syn_cnnc)
          (syn_wrex z A (.classEq (.cv z) (syn_cplc (.cv y) (syn_c1c))))))
      p0024 p0038
  have p0040 :=
    @g_dfrab2 (syn_wrex z A (.classEq (.cv z) (syn_cplc (.cv y) (syn_c1c)))) y (syn_cnnc)
      dv_cache_0015
  have p0041 := @g_vex y
  have p0042 :=
    @g_elimak z
      (syn_ccnvk (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                  (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                  (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                    (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
            (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      A (.cv y) dv_cache_0019 dv_cache_0005 dv_cache_0020 p0041
  have p0043 := @g_vex z
  have p0044 :=
    @g_opkelimagek (.cv y) (.cv z)
      (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
              (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
            (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
              (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
        (syn_cpw1 (syn_cpw1 (syn_c1c))))
      p0041 p0043
  have p0045 :=
    @g_opkelcnvk (.cv z) (.cv y)
      (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
              (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                  (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
          (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      p0043 p0041
  have p0046 := @g_dfaddc2 (.cv y) (syn_c1c)
  have p0047 :=
    @g_eqeq2i (syn_cplc (.cv y) (syn_c1c))
      (syn_cimak (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
              (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                  (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
          (syn_cpw1 (syn_cpw1 (syn_c1c)))) (.cv y))
      (.cv z) p0046
  have p0048 :=
    @g_n_3bitr4i
      (.classMem (syn_copk (.cv y) (.cv z)) (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                (syn_ccompl
                  (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                  (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                    (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
            (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      (.classEq (.cv z) (syn_cimak (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                  (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                  (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                    (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
            (syn_cpw1 (syn_cpw1 (syn_c1c)))) (.cv y)))
      (.classMem (syn_copk (.cv z) (.cv y)) (syn_ccnvk (syn_cimagek (syn_cimak (syn_cdif
                (syn_cins3k (syn_ccompl (syn_cimak
                      (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                  (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                    (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                      (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
              (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      (.classEq (.cv z) (syn_cplc (.cv y) (syn_c1c))) p0044 p0045 p0047
  have p0049 :=
    @g_rexbii
      (.classMem (syn_copk (.cv z) (.cv y)) (syn_ccnvk (syn_cimagek (syn_cimak (syn_cdif
                (syn_cins3k (syn_ccompl (syn_cimak
                      (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                  (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                    (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                      (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
              (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      (.classEq (.cv z) (syn_cplc (.cv y) (syn_c1c))) z A p0048
  have p0050 :=
    @g_bitri
      (.classMem (.cv y) (syn_cimak (syn_ccnvk (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                    (syn_ccompl (syn_cimak
                        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                    (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                      (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                        (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                (syn_cpw1 (syn_cpw1 (syn_c1c)))))) A))
      (syn_wrex z A (.classMem (syn_copk (.cv z) (.cv y)) (syn_ccnvk (syn_cimagek (syn_cimak
                (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                    (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                      (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                        (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      (syn_wrex z A (.classEq (.cv z) (syn_cplc (.cv y) (syn_c1c)))) p0042 p0049
  have p0051 :=
    @g_eqabi (syn_wrex z A (.classEq (.cv z) (syn_cplc (.cv y) (syn_c1c)))) y
      (syn_cimak (syn_ccnvk (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                      (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                  (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                    (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                      (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
              (syn_cpw1 (syn_cpw1 (syn_c1c)))))) A)
      dv_cache_0021 p0050
  have p0052 := @g_addcexlem
  have p0053 := @g_n_1cex
  have p0054 := @g_pw1ex (syn_c1c) p0053
  have p0055 := @g_pw1ex (syn_cpw1 (syn_c1c)) p0054
  have p0056 :=
    @g_imakex
      (syn_cdif (syn_cins3k (syn_ccompl
            (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
              (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
          (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
            (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
              (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      (syn_cpw1 (syn_cpw1 (syn_c1c))) p0052 p0055
  have p0057 :=
    @g_imagekex
      (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
              (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
            (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
              (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
        (syn_cpw1 (syn_cpw1 (syn_c1c))))
      p0056
  have p0058 :=
    @g_cnvkex
      (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
              (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                  (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
          (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      p0057
  have p0059 :=
    @g_imakex
      (syn_ccnvk (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                  (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                  (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                    (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
            (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      A p0058 hyp_phiall_1
  have p0060 :=
    @g_eqeltrri
      (syn_cimak (syn_ccnvk (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                      (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                  (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                    (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                      (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
              (syn_cpw1 (syn_cpw1 (syn_c1c)))))) A)
      (.cab y (syn_wrex z A (.classEq (.cv z) (syn_cplc (.cv y) (syn_c1c))))) (syn_cvv)
      p0051 p0059
  have p0061 := @g_nncex
  have p0062 :=
    @g_inex (.cab y (syn_wrex z A (.classEq (.cv z) (syn_cplc (.cv y) (syn_c1c)))))
      (syn_cnnc) p0060 p0061
  have p0063 :=
    @g_eqeltri
      (syn_crab y (syn_cnnc) (syn_wrex z A (.classEq (.cv z) (syn_cplc (.cv y) (syn_c1c)))))
      (syn_cin (.cab y (syn_wrex z A (.classEq (.cv z) (syn_cplc (.cv y) (syn_c1c)))))
        (syn_cnnc))
      (syn_cvv) p0040 p0062
  have p0064 :=
    @g_phieq (.cv x)
      (syn_crab y (syn_cnnc) (syn_wrex z A (.classEq (.cv z) (syn_cplc (.cv y) (syn_c1c)))))
  have p0065 :=
    @g_eqeq2d
      (.classEq (.cv x) (syn_crab y (syn_cnnc)
          (syn_wrex z A (.classEq (.cv z) (syn_cplc (.cv y) (syn_c1c))))))
      (syn_cphi (.cv x))
      (syn_cphi (syn_crab y (syn_cnnc)
          (syn_wrex z A (.classEq (.cv z) (syn_cplc (.cv y) (syn_c1c))))))
      A p0064
  have p0066 :=
    @g_spcev (.classEq A (syn_cphi (.cv x)))
      (.classEq A (syn_cphi (syn_crab y (syn_cnnc)
            (syn_wrex z A (.classEq (.cv z) (syn_cplc (.cv y) (syn_c1c)))))))
      x
      (syn_crab y (syn_cnnc) (syn_wrex z A (.classEq (.cv z) (syn_cplc (.cv y) (syn_c1c)))))
      dv_cache_0011 dv_cache_0022 p0063 p0065
  have p0067 :=
    @g_syl (syn_wa (syn_wss A (syn_cnnc)) (.neg (.classMem (syn_c0c) A)))
      (.classEq A (syn_cphi (syn_crab y (syn_cnnc)
            (syn_wrex z A (.classEq (.cv z) (syn_cplc (.cv y) (syn_c1c)))))))
      (syn_wex x (.classEq A (syn_cphi (.cv x)))) p0039 p0066
  exact p0067

@[expose]
noncomputable def g_phialllem2 (x : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (hyp_phiall_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf
      (.imp (.neg (.classMem (syn_c0c) A)) (syn_wex x (.classEq A (syn_cphi (.cv x))))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have dv_cache_0001 : y ∉ ((syn_cin A (syn_cnnc))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
          fresh_y_not_A, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((syn_cun (syn_cdif A (syn_cnnc)) (.cv y))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_A_x, fresh_x_ne_y, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0003 :
    x ∉ ((Wff.classEq A (syn_cphi (syn_cun (syn_cdif A (syn_cnnc)) (.cv y))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cphi,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_A_x, fresh_x_ne_y, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0004 : y ∉ ((syn_wex x (.classEq A (syn_cphi (.cv x))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cphi,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_y_not_A, fresh_y_ne_x, or_false, and_false,
          not_false_eq_true])
  have p0000 := @g_inss2 A (syn_cnnc)
  have p0001 := @g_inss1 A (syn_cnnc)
  have p0002 := @g_sseli (syn_cin A (syn_cnnc)) A (syn_c0c) p0001
  have p0003 :=
    @g_con3i (.classMem (syn_c0c) (syn_cin A (syn_cnnc))) (.classMem (syn_c0c) A) p0002
  have p0004 := @g_nncex
  have p0005 := @g_inex A (syn_cnnc) hyp_phiall_1 p0004
  have p0006 := @g_phialllem1 y (syn_cin A (syn_cnnc)) dv_cache_0001 p0005
  have p0007 :=
    @g_sylancr (.neg (.classMem (syn_c0c) A)) (syn_wss (syn_cin A (syn_cnnc)) (syn_cnnc))
      (.neg (.classMem (syn_c0c) (syn_cin A (syn_cnnc))))
      (syn_wex y (.classEq (syn_cin A (syn_cnnc)) (syn_cphi (.cv y)))) p0000 p0003 p0006
  have p0008 := @g_uncom (syn_cdif A (syn_cnnc)) (syn_cin A (syn_cnnc))
  have p0009 := @g_inundif A (syn_cnnc)
  have p0010 :=
    @g_eqtri (syn_cun (syn_cdif A (syn_cnnc)) (syn_cin A (syn_cnnc)))
      (syn_cun (syn_cin A (syn_cnnc)) (syn_cdif A (syn_cnnc))) A p0008 p0009
  have p0011 := @g_uneq2 (syn_cin A (syn_cnnc)) (syn_cphi (.cv y)) (syn_cdif A (syn_cnnc))
  have p0012 :=
    @g_syl5eqr (.classEq (syn_cin A (syn_cnnc)) (syn_cphi (.cv y))) A
      (syn_cun (syn_cdif A (syn_cnnc)) (syn_cin A (syn_cnnc)))
      (syn_cun (syn_cdif A (syn_cnnc)) (syn_cphi (.cv y))) p0010 p0011
  have p0013 := @g_phiun (syn_cdif A (syn_cnnc)) (.cv y)
  have p0014 := @g_incom (syn_cdif A (syn_cnnc)) (syn_cnnc)
  have p0015 := @g_disjdif (syn_cnnc) A
  have p0016 :=
    @g_eqtri (syn_cin (syn_cdif A (syn_cnnc)) (syn_cnnc))
      (syn_cin (syn_cnnc) (syn_cdif A (syn_cnnc))) (syn_c0) p0014 p0015
  have p0017 := @g_phidisjnn (syn_cdif A (syn_cnnc))
  have p0018 := Nominal.mp p0016 p0017
  have p0019 :=
    @g_uneq1i (syn_cphi (syn_cdif A (syn_cnnc))) (syn_cdif A (syn_cnnc))
      (syn_cphi (.cv y)) p0018
  have p0020 :=
    @g_eqtri (syn_cphi (syn_cun (syn_cdif A (syn_cnnc)) (.cv y)))
      (syn_cun (syn_cphi (syn_cdif A (syn_cnnc))) (syn_cphi (.cv y)))
      (syn_cun (syn_cdif A (syn_cnnc)) (syn_cphi (.cv y))) p0013 p0019
  have p0021 :=
    @g_syl6eqr (.classEq (syn_cin A (syn_cnnc)) (syn_cphi (.cv y))) A
      (syn_cun (syn_cdif A (syn_cnnc)) (syn_cphi (.cv y)))
      (syn_cphi (syn_cun (syn_cdif A (syn_cnnc)) (.cv y))) p0012 p0020
  have p0023 := @g_difex A (syn_cnnc) hyp_phiall_1 p0004
  have p0024 := @g_vex y
  have p0025 := @g_unex (syn_cdif A (syn_cnnc)) (.cv y) p0023 p0024
  have p0026 := @g_phieq (.cv x) (syn_cun (syn_cdif A (syn_cnnc)) (.cv y))
  have p0027 :=
    @g_eqeq2d (.classEq (.cv x) (syn_cun (syn_cdif A (syn_cnnc)) (.cv y)))
      (syn_cphi (.cv x)) (syn_cphi (syn_cun (syn_cdif A (syn_cnnc)) (.cv y))) A p0026
  have p0028 :=
    @g_spcev (.classEq A (syn_cphi (.cv x)))
      (.classEq A (syn_cphi (syn_cun (syn_cdif A (syn_cnnc)) (.cv y)))) x
      (syn_cun (syn_cdif A (syn_cnnc)) (.cv y)) dv_cache_0002 dv_cache_0003 p0025 p0027
  have p0029 :=
    @g_syl (.classEq (syn_cin A (syn_cnnc)) (syn_cphi (.cv y)))
      (.classEq A (syn_cphi (syn_cun (syn_cdif A (syn_cnnc)) (.cv y))))
      (syn_wex x (.classEq A (syn_cphi (.cv x)))) p0021 p0028
  have p0030 :=
    @g_exlimiv (.classEq (syn_cin A (syn_cnnc)) (syn_cphi (.cv y)))
      (syn_wex x (.classEq A (syn_cphi (.cv x)))) y dv_cache_0004 p0029
  have p0031 :=
    @g_syl (.neg (.classMem (syn_c0c) A))
      (syn_wex y (.classEq (syn_cin A (syn_cnnc)) (syn_cphi (.cv y))))
      (syn_wex x (.classEq A (syn_cphi (.cv x)))) p0007 p0030
  exact p0031

@[expose]
noncomputable def g_phiall (x : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (hyp_phiall_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf
      (syn_wex x (syn_wo (.classEq A (syn_cphi (.cv x)))
          (.classEq A (syn_cun (syn_cphi (.cv x)) (syn_csn (syn_c0c)))))) :=
  by
  have dv_cache_0001 : x ∉ ((syn_cdif A (syn_csn (syn_c0c)))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union, dv_A_x,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((Wff.classMem (syn_c0c) A)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union, dv_A_x,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have p0000 := @g_neldifsn (syn_c0c) A
  have p0001 := @g_snex (syn_c0c)
  have p0002 := @g_difex A (syn_csn (syn_c0c)) hyp_phiall_1 p0001
  have p0003 := @g_phialllem2 x (syn_cdif A (syn_csn (syn_c0c))) dv_cache_0001 p0002
  have p0004 := Nominal.mp p0000 p0003
  have p0005 := @g_disjsn (syn_cdif A (syn_csn (syn_c0c))) (syn_c0c)
  have p0006 :=
    @g_mpbir
      (.classEq (syn_cin (syn_cdif A (syn_csn (syn_c0c))) (syn_csn (syn_c0c))) (syn_c0))
      (.neg (.classMem (syn_c0c) (syn_cdif A (syn_csn (syn_c0c))))) p0000 p0005
  have p0007 := @g_n_0cnelphi (.cv x)
  have p0008 := @g_disjsn (syn_cphi (.cv x)) (syn_c0c)
  have p0009 :=
    @g_mpbir (.classEq (syn_cin (syn_cphi (.cv x)) (syn_csn (syn_c0c))) (syn_c0))
      (.neg (.classMem (syn_c0c) (syn_cphi (.cv x)))) p0007 p0008
  have p0010 :=
    @g_eqtr4i (syn_cin (syn_cdif A (syn_csn (syn_c0c))) (syn_csn (syn_c0c))) (syn_c0)
      (syn_cin (syn_cphi (.cv x)) (syn_csn (syn_c0c))) p0006 p0009
  have p0011 :=
    @g_biantru
      (.classEq (syn_cin (syn_cdif A (syn_csn (syn_c0c))) (syn_csn (syn_c0c)))
        (syn_cin (syn_cphi (.cv x)) (syn_csn (syn_c0c))))
      (.classEq (syn_cun (syn_cdif A (syn_csn (syn_c0c))) (syn_csn (syn_c0c)))
        (syn_cun (syn_cphi (.cv x)) (syn_csn (syn_c0c))))
      p0010
  have p0012 :=
    @g_unineq (syn_cdif A (syn_csn (syn_c0c))) (syn_cphi (.cv x)) (syn_csn (syn_c0c))
  have p0013 :=
    @g_bitri
      (.classEq (syn_cun (syn_cdif A (syn_csn (syn_c0c))) (syn_csn (syn_c0c)))
        (syn_cun (syn_cphi (.cv x)) (syn_csn (syn_c0c))))
      (syn_wa (.classEq (syn_cun (syn_cdif A (syn_csn (syn_c0c))) (syn_csn (syn_c0c)))
          (syn_cun (syn_cphi (.cv x)) (syn_csn (syn_c0c))))
        (.classEq (syn_cin (syn_cdif A (syn_csn (syn_c0c))) (syn_csn (syn_c0c)))
          (syn_cin (syn_cphi (.cv x)) (syn_csn (syn_c0c)))))
      (.classEq (syn_cdif A (syn_csn (syn_c0c))) (syn_cphi (.cv x))) p0011 p0012
  have p0014 := @g_difsnid A (syn_c0c)
  have p0015 :=
    @g_eqeq1d (.classMem (syn_c0c) A)
      (syn_cun (syn_cdif A (syn_csn (syn_c0c))) (syn_csn (syn_c0c))) A
      (syn_cun (syn_cphi (.cv x)) (syn_csn (syn_c0c))) p0014
  have p0016 :=
    @g_syl5bbr (.classEq (syn_cdif A (syn_csn (syn_c0c))) (syn_cphi (.cv x)))
      (.classEq (syn_cun (syn_cdif A (syn_csn (syn_c0c))) (syn_csn (syn_c0c)))
        (syn_cun (syn_cphi (.cv x)) (syn_csn (syn_c0c))))
      (.classMem (syn_c0c) A)
      (.classEq A (syn_cun (syn_cphi (.cv x)) (syn_csn (syn_c0c)))) p0013 p0015
  have p0017 :=
    @g_exbidv (.classMem (syn_c0c) A)
      (.classEq (syn_cdif A (syn_csn (syn_c0c))) (syn_cphi (.cv x)))
      (.classEq A (syn_cun (syn_cphi (.cv x)) (syn_csn (syn_c0c)))) x dv_cache_0002 p0016
  have p0018 :=
    @g_mpbii (.classMem (syn_c0c) A)
      (syn_wex x (.classEq (syn_cdif A (syn_csn (syn_c0c))) (syn_cphi (.cv x))))
      (syn_wex x (.classEq A (syn_cun (syn_cphi (.cv x)) (syn_csn (syn_c0c))))) p0004
      p0017
  have p0019 :=
    @g_olc (.classEq A (syn_cun (syn_cphi (.cv x)) (syn_csn (syn_c0c))))
      (.classEq A (syn_cphi (.cv x)))
  have p0020 :=
    @g_eximi (.classEq A (syn_cun (syn_cphi (.cv x)) (syn_csn (syn_c0c))))
      (syn_wo (.classEq A (syn_cphi (.cv x)))
        (.classEq A (syn_cun (syn_cphi (.cv x)) (syn_csn (syn_c0c)))))
      x p0019
  have p0021 :=
    @g_syl (.classMem (syn_c0c) A)
      (syn_wex x (.classEq A (syn_cun (syn_cphi (.cv x)) (syn_csn (syn_c0c)))))
      (syn_wex x (syn_wo (.classEq A (syn_cphi (.cv x)))
          (.classEq A (syn_cun (syn_cphi (.cv x)) (syn_csn (syn_c0c))))))
      p0018 p0020
  have p0022 := @g_phialllem2 x A dv_cache_0003 hyp_phiall_1
  have p0023 :=
    @g_orc (.classEq A (syn_cphi (.cv x)))
      (.classEq A (syn_cun (syn_cphi (.cv x)) (syn_csn (syn_c0c))))
  have p0024 :=
    @g_eximi (.classEq A (syn_cphi (.cv x)))
      (syn_wo (.classEq A (syn_cphi (.cv x)))
        (.classEq A (syn_cun (syn_cphi (.cv x)) (syn_csn (syn_c0c)))))
      x p0023
  have p0025 :=
    @g_syl (.neg (.classMem (syn_c0c) A)) (syn_wex x (.classEq A (syn_cphi (.cv x))))
      (syn_wex x (syn_wo (.classEq A (syn_cphi (.cv x)))
          (.classEq A (syn_cun (syn_cphi (.cv x)) (syn_csn (syn_c0c))))))
      p0022 p0024
  have p0026 :=
    @g_pm2_61i (.classMem (syn_c0c) A)
      (syn_wex x (syn_wo (.classEq A (syn_cphi (.cv x)))
          (.classEq A (syn_cun (syn_cphi (.cv x)) (syn_csn (syn_c0c))))))
      p0021 p0025
  exact p0026


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk010Compact001Part038`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_opeq (A : Class) :
    Nominal.NPrf (.classEq A (syn_cop (syn_cproj1 A) (syn_cproj2 A))) :=
  by
  let proofSupport : Finset Var := A.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (h)
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (h)
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y := Ne.symm fresh_y_ne_z
  have dv_cache_0001 : x ∉ ((syn_cproj1 A)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cproj1, fresh_x_not_A,
          not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_cproj1 A)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cproj1, fresh_y_not_A,
          not_false_eq_true])
  have dv_cache_0003 : x ∉ ((syn_cproj2 A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cproj2, fresh_x_not_A,
          not_false_eq_true])
  have dv_cache_0004 : y ∉ ((syn_cproj2 A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cproj2, fresh_y_not_A,
          not_false_eq_true])
  have dv_cache_0005 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0006 : z ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_A, not_false_eq_true])
  have dv_cache_0007 : y ∉ ((Class.cab z (.classMem (syn_cphi (.cv z)) A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cphi,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_y_ne_z, fresh_y_not_A, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0008 : z ∉ ((Wff.classMem (syn_cphi (.cv y)) A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cphi,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_y, fresh_z_not_A, or_false, not_false_eq_true])
  have dv_cache_0009 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0010 : y ∉ ((Wff.classMem (.cv x) A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_x, fresh_y_not_A, or_false, not_false_eq_true])
  have dv_cache_0011 :
    y ∉
      ((Class.cab z (.classMem (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c))) A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cphi,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_y_ne_z, fresh_y_not_A,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0012 :
    z ∉ ((Wff.classMem (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))) A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cphi,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_y, fresh_z_not_A, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0013 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0014 : y ∉ ((Class.cv x)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_x, not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_op x y
      (syn_cproj1 A) (syn_cproj2 A) dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005
  have p0001 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_proj1 z A
      dv_cache_0006
  have p0002 :=
    @g_rexeqi (.classEq (.cv x) (syn_cphi (.cv y))) y (syn_cproj1 A)
      (.cab z (.classMem (syn_cphi (.cv z)) A)) dv_cache_0002 dv_cache_0007 p0001
  have p0003 := @g_phieq (.cv z) (.cv y)
  have p0004_e00_recanon :
    Nominal.NPrf (.imp (.objEq z y) (.classEq (syn_cphi (.cv z)) (syn_cphi (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cphi syn_wrex syn_wex syn_wa syn_cif syn_wo syn_cnnc syn_cint syn_cplc
          syn_c1c
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0003
  have p0004 :=
    @g_eleq1d (.objEq z y) (syn_cphi (.cv z)) (syn_cphi (.cv y)) A p0004_e00_recanon
  have p0005 :=
    @g_rexab (.classMem (syn_cphi (.cv z)) A) (.classMem (syn_cphi (.cv y)) A)
      (.classEq (.cv x) (syn_cphi (.cv y))) y z dv_cache_0008 dv_cache_0009 p0004
  have p0006 :=
    @g_ancom (.classMem (syn_cphi (.cv y)) A) (.classEq (.cv x) (syn_cphi (.cv y)))
  have p0007 := @g_eleq1 (.cv x) (syn_cphi (.cv y)) A
  have p0008 :=
    @g_pm5_32i (.classEq (.cv x) (syn_cphi (.cv y))) (.classMem (.cv x) A)
      (.classMem (syn_cphi (.cv y)) A) p0007
  have p0009 :=
    @g_bitr4i
      (syn_wa (.classMem (syn_cphi (.cv y)) A) (.classEq (.cv x) (syn_cphi (.cv y))))
      (syn_wa (.classEq (.cv x) (syn_cphi (.cv y))) (.classMem (syn_cphi (.cv y)) A))
      (syn_wa (.classEq (.cv x) (syn_cphi (.cv y))) (.classMem (.cv x) A)) p0006 p0008
  have p0010 :=
    @g_exbii
      (syn_wa (.classMem (syn_cphi (.cv y)) A) (.classEq (.cv x) (syn_cphi (.cv y))))
      (syn_wa (.classEq (.cv x) (syn_cphi (.cv y))) (.classMem (.cv x) A)) y p0009
  have p0011 :=
    @g_n_19_41v (.classEq (.cv x) (syn_cphi (.cv y))) (.classMem (.cv x) A) y
      dv_cache_0010
  have p0012 :=
    @g_ancom (syn_wex y (.classEq (.cv x) (syn_cphi (.cv y)))) (.classMem (.cv x) A)
  have p0013 :=
    @g_n_3bitri
      (syn_wex y
        (syn_wa (.classMem (syn_cphi (.cv y)) A) (.classEq (.cv x) (syn_cphi (.cv y)))))
      (syn_wex y (syn_wa (.classEq (.cv x) (syn_cphi (.cv y))) (.classMem (.cv x) A)))
      (syn_wa (syn_wex y (.classEq (.cv x) (syn_cphi (.cv y)))) (.classMem (.cv x) A))
      (syn_wa (.classMem (.cv x) A) (syn_wex y (.classEq (.cv x) (syn_cphi (.cv y)))))
      p0010 p0011 p0012
  have p0014 :=
    @g_n_3bitri (syn_wrex y (syn_cproj1 A) (.classEq (.cv x) (syn_cphi (.cv y))))
      (syn_wrex y (.cab z (.classMem (syn_cphi (.cv z)) A))
        (.classEq (.cv x) (syn_cphi (.cv y))))
      (syn_wex y
        (syn_wa (.classMem (syn_cphi (.cv y)) A) (.classEq (.cv x) (syn_cphi (.cv y)))))
      (syn_wa (.classMem (.cv x) A) (syn_wex y (.classEq (.cv x) (syn_cphi (.cv y)))))
      p0002 p0005 p0013
  have p0015 :=
    @g_abbii (syn_wrex y (syn_cproj1 A) (.classEq (.cv x) (syn_cphi (.cv y))))
      (syn_wa (.classMem (.cv x) A) (syn_wex y (.classEq (.cv x) (syn_cphi (.cv y))))) x
      p0014
  have p0016 :=
    (Nominal.classEqRefl (syn_crab x A (syn_wex y (.classEq (.cv x) (syn_cphi (.cv y))))))
  have p0017 :=
    @g_eqtr4i (.cab x (syn_wrex y (syn_cproj1 A) (.classEq (.cv x) (syn_cphi (.cv y)))))
      (.cab x (syn_wa (.classMem (.cv x) A) (syn_wex y (.classEq (.cv x) (syn_cphi (.cv y))))))
      (syn_crab x A (syn_wex y (.classEq (.cv x) (syn_cphi (.cv y))))) p0015 p0016
  have p0018 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_proj2 z A
      dv_cache_0006
  have p0019 :=
    @g_rexeqi (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c)))) y
      (syn_cproj2 A)
      (.cab z (.classMem (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c))) A))
      dv_cache_0004 dv_cache_0011 p0018
  have p0020_e00_recanon :
    Nominal.NPrf (.imp (.objEq z y) (.classEq (syn_cphi (.cv z)) (syn_cphi (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cphi syn_wrex syn_wex syn_wa syn_cif syn_wo syn_cnnc syn_cint syn_cplc
          syn_c1c
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0003
  have p0020 :=
    @g_uneq1d (.objEq z y) (syn_cphi (.cv z)) (syn_cphi (.cv y)) (syn_csn (syn_c0c))
      p0020_e00_recanon
  have p0021 :=
    @g_eleq1d (.objEq z y) (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c)))
      (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))) A p0020
  have p0022 :=
    @g_rexab (.classMem (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c))) A)
      (.classMem (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))) A)
      (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c)))) y z
      dv_cache_0012 dv_cache_0009 p0021
  have p0023 :=
    @g_ancom (.classMem (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))) A)
      (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))))
  have p0024 := @g_eleq1 (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))) A
  have p0025 :=
    @g_pm5_32i (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))))
      (.classMem (.cv x) A) (.classMem (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))) A)
      p0024
  have p0026 :=
    @g_bitr4i
      (syn_wa (.classMem (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))) A)
        (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c)))))
      (syn_wa (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))))
        (.classMem (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))) A))
      (syn_wa (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))))
        (.classMem (.cv x) A))
      p0023 p0025
  have p0027 :=
    @g_exbii
      (syn_wa (.classMem (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))) A)
        (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c)))))
      (syn_wa (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))))
        (.classMem (.cv x) A))
      y p0026
  have p0028 :=
    @g_n_19_41v (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))))
      (.classMem (.cv x) A) y dv_cache_0010
  have p0029 :=
    @g_ancom
      (syn_wex y (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c)))))
      (.classMem (.cv x) A)
  have p0030 :=
    @g_n_3bitri
      (syn_wex y (syn_wa (.classMem (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))) A)
          (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))))))
      (syn_wex y (syn_wa (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))))
          (.classMem (.cv x) A)))
      (syn_wa (syn_wex y (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c)))))
        (.classMem (.cv x) A))
      (syn_wa (.classMem (.cv x) A)
        (syn_wex y (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))))))
      p0027 p0028 p0029
  have p0031 :=
    @g_n_3bitri
      (syn_wrex y (syn_cproj2 A)
        (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c)))))
      (syn_wrex y (.cab z (.classMem (syn_cun (syn_cphi (.cv z)) (syn_csn (syn_c0c))) A))
        (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c)))))
      (syn_wex y (syn_wa (.classMem (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))) A)
          (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))))))
      (syn_wa (.classMem (.cv x) A)
        (syn_wex y (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))))))
      p0019 p0022 p0030
  have p0032 :=
    @g_abbii
      (syn_wrex y (syn_cproj2 A)
        (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c)))))
      (syn_wa (.classMem (.cv x) A)
        (syn_wex y (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))))))
      x p0031
  have p0033 :=
    (Nominal.classEqRefl (syn_crab x A
        (syn_wex y (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c)))))))
  have p0034 :=
    @g_eqtr4i
      (.cab x (syn_wrex y (syn_cproj2 A)
          (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))))))
      (.cab x (syn_wa (.classMem (.cv x) A) (syn_wex y
            (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c)))))))
      (syn_crab x A
        (syn_wex y (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))))))
      p0032 p0033
  have p0035 :=
    @g_uneq12i (.cab x (syn_wrex y (syn_cproj1 A) (.classEq (.cv x) (syn_cphi (.cv y)))))
      (syn_crab x A (syn_wex y (.classEq (.cv x) (syn_cphi (.cv y)))))
      (.cab x (syn_wrex y (syn_cproj2 A)
          (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))))))
      (syn_crab x A
        (syn_wex y (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))))))
      p0017 p0034
  have p0036 :=
    @g_unrab (syn_wex y (.classEq (.cv x) (syn_cphi (.cv y))))
      (syn_wex y (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))))) x A
  have p0037 :=
    @g_rabid2
      (syn_wo (syn_wex y (.classEq (.cv x) (syn_cphi (.cv y))))
        (syn_wex y (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))))))
      x A dv_cache_0013
  have p0038 := @g_vex x
  have p0039 := @g_phiall y (.cv x) dv_cache_0014 p0038
  have p0040 :=
    @g_n_19_43 (.classEq (.cv x) (syn_cphi (.cv y)))
      (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c)))) y
  have p0041 :=
    @g_mpbi
      (syn_wex y (syn_wo (.classEq (.cv x) (syn_cphi (.cv y)))
          (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))))))
      (syn_wo (syn_wex y (.classEq (.cv x) (syn_cphi (.cv y))))
        (syn_wex y (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))))))
      p0039 p0040
  have p0042 :=
    @g_a1i
      (syn_wo (syn_wex y (.classEq (.cv x) (syn_cphi (.cv y))))
        (syn_wex y (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))))))
      (.classMem (.cv x) A) p0041
  have p0043 :=
    @g_mprgbir
      (.classEq A (syn_crab x A (syn_wo (syn_wex y (.classEq (.cv x) (syn_cphi (.cv y))))
            (syn_wex y (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))))))))
      (syn_wo (syn_wex y (.classEq (.cv x) (syn_cphi (.cv y))))
        (syn_wex y (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))))))
      x A p0037 p0042
  have p0044 :=
    @g_eqtr4i
      (syn_cun (syn_crab x A (syn_wex y (.classEq (.cv x) (syn_cphi (.cv y))))) (syn_crab x A
          (syn_wex y (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c)))))))
      (syn_crab x A (syn_wo (syn_wex y (.classEq (.cv x) (syn_cphi (.cv y)))) (syn_wex y
            (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c)))))))
      A p0036 p0043
  have p0045 :=
    @g_n_3eqtrri (syn_cop (syn_cproj1 A) (syn_cproj2 A))
      (syn_cun (.cab x (syn_wrex y (syn_cproj1 A) (.classEq (.cv x) (syn_cphi (.cv y)))))
        (.cab x (syn_wrex y (syn_cproj2 A)
            (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c)))))))
      (syn_cun (syn_crab x A (syn_wex y (.classEq (.cv x) (syn_cphi (.cv y))))) (syn_crab x A
          (syn_wex y (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c)))))))
      A p0000 p0035 p0044
  exact p0045

@[expose]
noncomputable def g_opeqexb (x : Var) (y : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (syn_wb (.classMem A (syn_cvv))
        (syn_wex x (syn_wex y (.classEq A (syn_cop (.cv x) (.cv y)))))) :=
  by
  have dv_cache_0001 : y ∉ ((Wff.classEq (.cv x) (syn_cproj1 A))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cproj1, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_x_y), dv_A_y, or_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((Wff.classEq (.cv y) (syn_cproj2 A))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cproj2, Finset.mem_union,
          Finset.mem_singleton, dv_x_y, dv_A_x, or_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((syn_cproj1 A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cproj1, dv_A_x,
          not_false_eq_true])
  have dv_cache_0004 : y ∉ ((syn_cproj2 A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cproj2, dv_A_y,
          not_false_eq_true])
  have p0000 := @g_opexb (syn_cproj1 A) (syn_cproj2 A)
  have p0001 := @g_opeq A
  have p0002 := @g_eleq1i A (syn_cop (syn_cproj1 A) (syn_cproj2 A)) (syn_cvv) p0001
  have p0003 :=
    @g_eeanv (.classEq (.cv x) (syn_cproj1 A)) (.classEq (.cv y) (syn_cproj2 A)) x y
      dv_cache_0001 dv_cache_0002
  have p0004 :=
    @g_eqeq1i A (syn_cop (syn_cproj1 A) (syn_cproj2 A)) (syn_cop (.cv x) (.cv y)) p0001
  have p0005 := @g_eqcom (syn_cop (syn_cproj1 A) (syn_cproj2 A)) (syn_cop (.cv x) (.cv y))
  have p0006 := @g_opth (.cv x) (.cv y) (syn_cproj1 A) (syn_cproj2 A)
  have p0007 :=
    @g_n_3bitri (.classEq A (syn_cop (.cv x) (.cv y)))
      (.classEq (syn_cop (syn_cproj1 A) (syn_cproj2 A)) (syn_cop (.cv x) (.cv y)))
      (.classEq (syn_cop (.cv x) (.cv y)) (syn_cop (syn_cproj1 A) (syn_cproj2 A)))
      (syn_wa (.classEq (.cv x) (syn_cproj1 A)) (.classEq (.cv y) (syn_cproj2 A))) p0004
      p0005 p0006
  have p0008 :=
    @g_n_2exbii (.classEq A (syn_cop (.cv x) (.cv y)))
      (syn_wa (.classEq (.cv x) (syn_cproj1 A)) (.classEq (.cv y) (syn_cproj2 A))) x y
      p0007
  have p0009 := @g_isset x (syn_cproj1 A) dv_cache_0003
  have p0010 := @g_isset y (syn_cproj2 A) dv_cache_0004
  have p0011 :=
    @g_anbi12i (.classMem (syn_cproj1 A) (syn_cvv))
      (syn_wex x (.classEq (.cv x) (syn_cproj1 A))) (.classMem (syn_cproj2 A) (syn_cvv))
      (syn_wex y (.classEq (.cv y) (syn_cproj2 A))) p0009 p0010
  have p0012 :=
    @g_n_3bitr4i
      (syn_wex x (syn_wex y
          (syn_wa (.classEq (.cv x) (syn_cproj1 A)) (.classEq (.cv y) (syn_cproj2 A)))))
      (syn_wa (syn_wex x (.classEq (.cv x) (syn_cproj1 A)))
        (syn_wex y (.classEq (.cv y) (syn_cproj2 A))))
      (syn_wex x (syn_wex y (.classEq A (syn_cop (.cv x) (.cv y)))))
      (syn_wa (.classMem (syn_cproj1 A) (syn_cvv)) (.classMem (syn_cproj2 A) (syn_cvv)))
      p0003 p0008 p0011
  have p0013 :=
    @g_n_3bitr4i (.classMem (syn_cop (syn_cproj1 A) (syn_cproj2 A)) (syn_cvv))
      (syn_wa (.classMem (syn_cproj1 A) (syn_cvv)) (.classMem (syn_cproj2 A) (syn_cvv)))
      (.classMem A (syn_cvv))
      (syn_wex x (syn_wex y (.classEq A (syn_cop (.cv x) (.cv y))))) p0000 p0002 p0012
  exact p0013

@[expose]
noncomputable def g_opeqex (x : Var) (y : Var) (A : Class) (V : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.imp (.classMem A V) (syn_wex x (syn_wex y (.classEq A (syn_cop (.cv x) (.cv y)))))) :=
  by
  have dv_cache_0001 : x ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have dv_cache_0002 : y ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_y, not_false_eq_true])
  have dv_cache_0003 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show x ≠ y from (by exact dv_x_y))
  have p0000 := @g_elex A V
  have p0001 := @g_opeqexb x y A dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0002 :=
    @g_sylib (.classMem A V) (.classMem A (syn_cvv))
      (syn_wex x (syn_wex y (.classEq A (syn_cop (.cv x) (.cv y))))) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_opabbid (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (hyp_opabbid_1 : Nominal.NPrf (syn_wnf x ph))
    (hyp_opabbid_2 : Nominal.NPrf (syn_wnf y ph))
    (hyp_opabbid_3 : Nominal.NPrf (.imp ph (syn_wb ps ch))) :
    Nominal.NPrf (.imp ph (.classEq (syn_copab x y ps) (syn_copab x y ch))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_not_ph : z ∉ ph.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_z_not_ps : z ∉ ps.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_z_not_ch : z ∉ ch.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_y_ne_z : y ≠ z := Ne.symm fresh_z_ne_y
  have dv_cache_0001 : z ∉ (ph).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_ph, not_false_eq_true])
  have dv_cache_0002 : z ∉ (ps).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_ps, not_false_eq_true])
  have dv_cache_0003 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0004 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0005 : z ∉ (ch).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_ch, not_false_eq_true])
  have p0000 :=
    @g_anbi2d ph ps ch (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) hyp_opabbid_3
  have p0001 :=
    @g_exbid ph (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) ps)
      (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) ch) y hyp_opabbid_2 p0000
  have p0002 :=
    @g_exbid ph (syn_wex y (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) ps))
      (syn_wex y (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) ch)) x hyp_opabbid_1
      p0001
  have p0003 :=
    @g_abbidv ph
      (syn_wex x (syn_wex y (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) ps)))
      (syn_wex x (syn_wex y (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) ch))) z
      dv_cache_0001 p0002
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_opab ps x y z
      dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0005 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_opab ch x y z
      dv_cache_0005 dv_cache_0003 dv_cache_0004
  have p0006 :=
    @g_n_3eqtr4g ph
      (.cab z (syn_wex x (syn_wex y (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) ps))))
      (.cab z (syn_wex x (syn_wex y (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) ch))))
      (syn_copab x y ps) (syn_copab x y ch) p0003 p0004 p0005
  exact p0006

@[expose]
noncomputable def g_opabbidv (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (dv_ph_x : x ∉ ph.fv) (dv_ph_y : y ∉ ph.fv)
    (hyp_opabbidv_1 : Nominal.NPrf (.imp ph (syn_wb ps ch))) :
    Nominal.NPrf (.imp ph (.classEq (syn_copab x y ps) (syn_copab x y ch))) :=
  by
  have dv_cache_0001 : x ∉ (ph).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_ph_x, not_false_eq_true])
  have dv_cache_0002 : y ∉ (ph).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_ph_y, not_false_eq_true])
  have p0000 := @g_nfv ph x dv_cache_0001
  have p0001 := @g_nfv ph y dv_cache_0002
  have p0002 := @g_opabbid ph ps ch x y p0000 p0001 hyp_opabbidv_1
  exact p0002

@[expose]
noncomputable def g_opabbii (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (hyp_opabbii_1 : Nominal.NPrf (syn_wb ph ps)) :
    Nominal.NPrf (.classEq (syn_copab x y ph) (syn_copab x y ps)) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_y_ne_z : y ≠ z := Ne.symm fresh_z_ne_y
  have dv_cache_0001 : x ∉ ((Wff.classEq (.cv z) (.cv z))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_z, or_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((Wff.classEq (.cv z) (.cv z))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_z, or_false, not_false_eq_true])
  have p0000 := @g_eqid (.cv z)
  have p0001 := @g_a1i (syn_wb ph ps) (.classEq (.cv z) (.cv z)) hyp_opabbii_1
  have p0002 :=
    @g_opabbidv (.classEq (.cv z) (.cv z)) ph ps x y dv_cache_0001 dv_cache_0002 p0001
  have p0003 := Nominal.mp p0000 p0002
  exact p0003

@[expose]
noncomputable def g_nfopab (ph : Wff) (x : Var) (y : Var) (z : Var) (dv_x_z : x ≠ z)
    (dv_y_z : y ≠ z) (hyp_nfopab_1 : Nominal.NPrf (syn_wnf z ph)) :
    Nominal.NPrf (syn_wnfc z (syn_copab x y ph)) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var)
  let w : Var := freshVar proofSupport 0
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_w_not_ph : w ∉ ph.fv := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_w : x ≠ w := Ne.symm fresh_w_ne_x
  have fresh_w_ne_y : w ≠ y := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_y_ne_w : y ≠ w := Ne.symm fresh_w_ne_y
  have fresh_w_ne_z : w ≠ z := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_z_ne_w : z ≠ w := Ne.symm fresh_w_ne_z
  have dv_cache_0001 : w ∉ (ph).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_ph, not_false_eq_true])
  have dv_cache_0002 : x ≠ w := by
    clear dv_cache_0001
    exact (show x ≠ w from (by exact fresh_x_ne_w))
  have dv_cache_0003 : y ≠ w :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show y ≠ w from (by exact fresh_y_ne_w))
  have dv_cache_0004 : z ∉ ((Wff.classEq (.cv w) (syn_cop (.cv x) (.cv y)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_w, (Ne.symm dv_x_z), (Ne.symm dv_y_z),
          or_false, not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_opab ph x y w
      dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 := @g_nfv (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) z dv_cache_0004
  have p0002 :=
    @g_nfan (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph z p0001 hyp_nfopab_1
  have p0003 := @g_nfex (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph) z y p0002
  have p0004 :=
    @g_nfex (syn_wex y (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph)) z x p0003
  have p0005 :=
    @g_nfab
      (syn_wex x (syn_wex y (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph))) z w
      p0004
  have p0006 :=
    @g_nfcxfr z (syn_copab x y ph)
      (.cab w (syn_wex x (syn_wex y (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph))))
      p0000 p0005
  exact p0006

@[expose]
noncomputable def g_nfopab1 (ph : Wff) (x : Var) (y : Var) :
    Nominal.NPrf (syn_wnfc x (syn_copab x y ph)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_not_ph : z ∉ ph.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_y_ne_z : y ≠ z := Ne.symm fresh_z_ne_y
  have dv_cache_0001 : z ∉ (ph).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_ph, not_false_eq_true])
  have dv_cache_0002 : x ≠ z := by
    clear dv_cache_0001
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0003 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_opab ph x y z
      dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    @g_nfe1 (syn_wex y (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) ph)) x
  have p0002 :=
    @g_nfab
      (syn_wex x (syn_wex y (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) ph))) x z
      p0001
  have p0003 :=
    @g_nfcxfr x (syn_copab x y ph)
      (.cab z (syn_wex x (syn_wex y (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) ph))))
      p0000 p0002
  exact p0003

@[expose]
noncomputable def g_nfopab2 (ph : Wff) (x : Var) (y : Var) :
    Nominal.NPrf (syn_wnfc y (syn_copab x y ph)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_not_ph : z ∉ ph.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_y_ne_z : y ≠ z := Ne.symm fresh_z_ne_y
  have dv_cache_0001 : z ∉ (ph).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_ph, not_false_eq_true])
  have dv_cache_0002 : x ≠ z := by
    clear dv_cache_0001
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0003 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_opab ph x y z
      dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 := @g_nfe1 (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) ph) y
  have p0002 :=
    @g_nfex (syn_wex y (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) ph)) y x p0001
  have p0003 :=
    @g_nfab
      (syn_wex x (syn_wex y (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) ph))) y z
      p0002
  have p0004 :=
    @g_nfcxfr y (syn_copab x y ph)
      (.cab z (syn_wex x (syn_wex y (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) ph))))
      p0000 p0003
  exact p0004

@[expose]
noncomputable def g_cbvopab1 (ph : Wff) (ps : Wff) (x : Var) (y : Var) (z : Var)
    (dv_x_y : x ≠ y) (dv_y_z : y ≠ z) (hyp_cbvopab1_1 : Nominal.NPrf (syn_wnf z ph))
    (hyp_cbvopab1_2 : Nominal.NPrf (syn_wnf x ps))
    (hyp_cbvopab1_3 : Nominal.NPrf (.imp (.objEq x z) (syn_wb ph ps))) :
    Nominal.NPrf (.classEq (syn_copab x y ph) (syn_copab z y ps)) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var)
  let w : Var := freshVar proofSupport 0
  let v : Var := freshVar proofSupport 1
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_w_not_ph : w ∉ ph.fv := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_w_not_ps : w ∉ ps.fv := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_w : x ≠ w := Ne.symm fresh_w_ne_x
  have fresh_w_ne_y : w ≠ y := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_y_ne_w : y ≠ w := Ne.symm fresh_w_ne_y
  have fresh_w_ne_z : w ≠ z := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_z_ne_w : z ≠ w := Ne.symm fresh_w_ne_z
  have fresh_v : v ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_v_not_ph : v ∉ ph.fv := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_v_not_ps : v ∉ ps.fv := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_v_ne_x : v ≠ x := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_v : x ≠ v := Ne.symm fresh_v_ne_x
  have fresh_v_ne_y : v ≠ y := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_y_ne_v : y ≠ v := Ne.symm fresh_v_ne_y
  have fresh_v_ne_z : v ≠ z := by
    intro h
    exact fresh_v (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_z_ne_v : z ≠ v := Ne.symm fresh_v_ne_z
  have fresh_w_ne_v : w ≠ v :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_v_ne_w : v ≠ w := Ne.symm fresh_w_ne_v
  have dv_cache_0001 :
    v ∉ ((syn_wex y (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_v_ne_w, fresh_v_ne_x,
          fresh_v_ne_y, fresh_v_not_ph, or_false, and_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((Wff.classEq (.cv w) (syn_cop (.cv v) (.cv y)))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_w, fresh_x_ne_v, dv_x_y, or_false,
          not_false_eq_true])
  have dv_cache_0003 : x ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show x ≠ v from (by exact fresh_x_ne_v))
  have dv_cache_0004 : y ∉ ((Wff.classEq (.cv x) (.cv v))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_x_y), fresh_y_ne_v, or_false,
          not_false_eq_true])
  have dv_cache_0005 : z ∉ ((Wff.classEq (.cv w) (syn_cop (.cv v) (.cv y)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_w, fresh_z_ne_v, (Ne.symm dv_y_z), or_false,
          not_false_eq_true])
  have dv_cache_0006 : v ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show v ≠ z from (by exact fresh_v_ne_z))
  have dv_cache_0007 :
    v ∉ ((syn_wex y (syn_wa (.classEq (.cv w) (syn_cop (.cv z) (.cv y))) ps))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_v_ne_w, fresh_v_ne_z,
          fresh_v_ne_y, fresh_v_not_ps, or_false, and_false, not_false_eq_true])
  have dv_cache_0008 : y ∉ ((Wff.classEq (.cv v) (.cv z))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_v, dv_y_z, or_false, not_false_eq_true])
  have dv_cache_0009 : w ∉ (ph).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_ph, not_false_eq_true])
  have dv_cache_0010 : x ≠ w :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show x ≠ w from (by exact fresh_x_ne_w))
  have dv_cache_0011 : y ≠ w :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show y ≠ w from (by exact fresh_y_ne_w))
  have dv_cache_0012 : w ∉ (ps).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_ps, not_false_eq_true])
  have dv_cache_0013 : z ≠ w :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact (show z ≠ w from (by exact fresh_z_ne_w))
  have p0000 :=
    @g_nfv (syn_wex y (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph)) v
      dv_cache_0001
  have p0001 := @g_nfv (.classEq (.cv w) (syn_cop (.cv v) (.cv y))) x dv_cache_0002
  have p0002 := @g_nfs1v ph x v dv_cache_0003
  have p0003 :=
    @g_nfan (.classEq (.cv w) (syn_cop (.cv v) (.cv y))) (syn_wsb v x ph) x p0001 p0002
  have p0004 :=
    @g_nfex (syn_wa (.classEq (.cv w) (syn_cop (.cv v) (.cv y))) (syn_wsb v x ph)) x y
      p0003
  have p0005 := @g_opeq1 (.cv x) (.cv v) (.cv y)
  have p0006 :=
    @g_eqeq2d (.classEq (.cv x) (.cv v)) (syn_cop (.cv x) (.cv y))
      (syn_cop (.cv v) (.cv y)) (.cv w) p0005
  have p0007 := @g_sbequ12 ph x v
  have p0008_e01_recanon :
    Nominal.NPrf (.imp (.classEq (.cv x) (.cv v)) (syn_wb ph (syn_wsb v x ph))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wsb syn_wa syn_wex
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0007
  have p0008 :=
    @g_anbi12d (.classEq (.cv x) (.cv v)) (.classEq (.cv w) (syn_cop (.cv x) (.cv y)))
      (.classEq (.cv w) (syn_cop (.cv v) (.cv y))) ph (syn_wsb v x ph) p0006
      p0008_e01_recanon
  have p0009 :=
    @g_exbidv (.classEq (.cv x) (.cv v))
      (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph)
      (syn_wa (.classEq (.cv w) (syn_cop (.cv v) (.cv y))) (syn_wsb v x ph)) y
      dv_cache_0004 p0008
  have p0010_e02_recanon :
    Nominal.NPrf
      (.imp (.objEq x v)
        (syn_wb (syn_wex y (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph)) (syn_wex y
            (syn_wa (.classEq (.cv w) (syn_cop (.cv v) (.cv y))) (syn_wsb v x ph))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wex syn_wa syn_cop syn_cun syn_cnin syn_wnan syn_ccompl syn_wrex
          syn_cphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0009
  have p0010 :=
    @g_cbvex (syn_wex y (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph))
      (syn_wex y (syn_wa (.classEq (.cv w) (syn_cop (.cv v) (.cv y))) (syn_wsb v x ph))) x
      v p0000 p0004 p0010_e02_recanon
  have p0011 := @g_nfv (.classEq (.cv w) (syn_cop (.cv v) (.cv y))) z dv_cache_0005
  have p0012 := @g_nfsb ph x v z dv_cache_0006 hyp_cbvopab1_1
  have p0013 :=
    @g_nfan (.classEq (.cv w) (syn_cop (.cv v) (.cv y))) (syn_wsb v x ph) z p0011 p0012
  have p0014 :=
    @g_nfex (syn_wa (.classEq (.cv w) (syn_cop (.cv v) (.cv y))) (syn_wsb v x ph)) z y
      p0013
  have p0015 :=
    @g_nfv (syn_wex y (syn_wa (.classEq (.cv w) (syn_cop (.cv z) (.cv y))) ps)) v
      dv_cache_0007
  have p0016 := @g_opeq1 (.cv v) (.cv z) (.cv y)
  have p0017 :=
    @g_eqeq2d (.classEq (.cv v) (.cv z)) (syn_cop (.cv v) (.cv y))
      (syn_cop (.cv z) (.cv y)) (.cv w) p0016
  have p0018 := @g_sbequ ph v z x
  have p0019 := @g_sbie ph ps x z hyp_cbvopab1_2 hyp_cbvopab1_3
  have p0020_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv v) (.cv z)) (syn_wb (syn_wsb v x ph) (syn_wsb z x ph))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wsb syn_wa syn_wex
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0018
  have p0020 :=
    @g_syl6bb (.classEq (.cv v) (.cv z)) (syn_wsb v x ph) (syn_wsb z x ph) ps
      p0020_e00_recanon p0019
  have p0021 :=
    @g_anbi12d (.classEq (.cv v) (.cv z)) (.classEq (.cv w) (syn_cop (.cv v) (.cv y)))
      (.classEq (.cv w) (syn_cop (.cv z) (.cv y))) (syn_wsb v x ph) ps p0017 p0020
  have p0022 :=
    @g_exbidv (.classEq (.cv v) (.cv z))
      (syn_wa (.classEq (.cv w) (syn_cop (.cv v) (.cv y))) (syn_wsb v x ph))
      (syn_wa (.classEq (.cv w) (syn_cop (.cv z) (.cv y))) ps) y dv_cache_0008 p0021
  have p0023_e02_recanon :
    Nominal.NPrf
      (.imp (.objEq v z) (syn_wb (syn_wex y
            (syn_wa (.classEq (.cv w) (syn_cop (.cv v) (.cv y))) (syn_wsb v x ph)))
          (syn_wex y (syn_wa (.classEq (.cv w) (syn_cop (.cv z) (.cv y))) ps)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wex syn_wa syn_cop syn_cun syn_cnin syn_wnan syn_ccompl syn_wrex
          syn_cphi syn_wsb
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0022
  have p0023 :=
    @g_cbvex
      (syn_wex y (syn_wa (.classEq (.cv w) (syn_cop (.cv v) (.cv y))) (syn_wsb v x ph)))
      (syn_wex y (syn_wa (.classEq (.cv w) (syn_cop (.cv z) (.cv y))) ps)) v z p0014 p0015
      p0023_e02_recanon
  have p0024 :=
    @g_bitri
      (syn_wex x (syn_wex y (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph)))
      (syn_wex v (syn_wex y
          (syn_wa (.classEq (.cv w) (syn_cop (.cv v) (.cv y))) (syn_wsb v x ph))))
      (syn_wex z (syn_wex y (syn_wa (.classEq (.cv w) (syn_cop (.cv z) (.cv y))) ps)))
      p0010 p0023
  have p0025 :=
    @g_abbii
      (syn_wex x (syn_wex y (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph)))
      (syn_wex z (syn_wex y (syn_wa (.classEq (.cv w) (syn_cop (.cv z) (.cv y))) ps))) w
      p0024
  have p0026 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_opab ph x y w
      dv_cache_0009 dv_cache_0010 dv_cache_0011
  have p0027 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_opab ps z y w
      dv_cache_0012 dv_cache_0013 dv_cache_0011
  have p0028 :=
    @g_n_3eqtr4i
      (.cab w (syn_wex x (syn_wex y (syn_wa (.classEq (.cv w) (syn_cop (.cv x) (.cv y))) ph))))
      (.cab w (syn_wex z (syn_wex y (syn_wa (.classEq (.cv w) (syn_cop (.cv z) (.cv y))) ps))))
      (syn_copab x y ph) (syn_copab z y ps) p0025 p0026 p0027
  exact p0028


end NFChoice.DirectNominalPrf.WPPReplay

end

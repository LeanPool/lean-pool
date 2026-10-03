/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk012BCompact001Block003

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk012BCompact001Part015`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_cbvmpt (x : Var) (y : Var) (A : Class) (B : Class) (C : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (hyp_cbvmpt_1 : Nominal.NPrf (syn_wnfc y B))
    (hyp_cbvmpt_2 : Nominal.NPrf (syn_wnfc x C))
    (hyp_cbvmpt_3 : Nominal.NPrf (.imp (.objEq x y) (.classEq B C))) :
    Nominal.NPrf (.classEq (syn_cmpt x A B) (syn_cmpt y A C)) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv
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
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_y_ne_z : y ≠ z := Ne.symm fresh_z_ne_y
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_C : z ∉ C.fv := by
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
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_x_ne_w : x ≠ w := Ne.symm fresh_w_ne_x
  have fresh_w_ne_y : w ≠ y := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_y_ne_w : y ≠ w := Ne.symm fresh_w_ne_y
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_w_not_B : w ∉ B.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_w_not_C : w ∉ C.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have fresh_z_ne_w : z ≠ w :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_w_ne_z : w ≠ z := Ne.symm fresh_z_ne_w
  have dv_cache_0001 : w ∉ ((syn_wa (.classMem (.cv x) A) (.classEq (.cv z) B))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_x, fresh_w_not_A, fresh_w_ne_z, fresh_w_not_B,
          or_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((Wff.classMem (.cv w) A)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_w, dv_A_x, or_false, not_false_eq_true])
  have dv_cache_0003 : x ≠ w :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show x ≠ w from (by exact fresh_x_ne_w))
  have dv_cache_0004 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0005 : z ≠ w :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show z ≠ w from (by exact fresh_z_ne_w))
  have dv_cache_0006 : y ∉ ((Wff.classMem (.cv w) A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_w, dv_A_y, or_false, not_false_eq_true])
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
  have dv_cache_0008 : w ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show w ≠ y from (by exact fresh_w_ne_y))
  have dv_cache_0009 : w ∉ ((syn_wa (.classMem (.cv y) A) (.classEq (.cv z) C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_y, fresh_w_not_A, fresh_w_ne_z, fresh_w_not_C,
          or_false, not_false_eq_true])
  have dv_cache_0010 : x ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_z, not_false_eq_true])
  have dv_cache_0011 : w ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show w ≠ z from (by exact fresh_w_ne_z))
  have dv_cache_0012 : z ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show z ≠ y from (by exact fresh_z_ne_y))
  have dv_cache_0013 : z ∉ (A).fv :=
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
        simp only [fresh_z_not_A, not_false_eq_true])
  have dv_cache_0014 : z ∉ (B).fv :=
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
        simp only [fresh_z_not_B, not_false_eq_true])
  have dv_cache_0015 : z ∉ (C).fv :=
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
        simp only [fresh_z_not_C, not_false_eq_true])
  have dv_cache_0016 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have p0000 := @g_nfv (syn_wa (.classMem (.cv x) A) (.classEq (.cv z) B)) w dv_cache_0001
  have p0001 := @g_nfv (.classMem (.cv w) A) x dv_cache_0002
  have p0002 := @g_nfs1v (.classEq (.cv z) B) x w dv_cache_0003
  have p0003 :=
    @g_nfan (.classMem (.cv w) A) (syn_wsb w x (.classEq (.cv z) B)) x p0001 p0002
  have p0004 := @g_eleq1 (.cv x) (.cv w) A
  have p0005 := @g_sbequ12 (.classEq (.cv z) B) x w
  have p0006_e01_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv x) (.cv w))
        (syn_wb (.classEq (.cv z) B) (syn_wsb w x (.classEq (.cv z) B)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wsb syn_wa syn_wex
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0005
  have p0006 :=
    @g_anbi12d (.classEq (.cv x) (.cv w)) (.classMem (.cv x) A) (.classMem (.cv w) A)
      (.classEq (.cv z) B) (syn_wsb w x (.classEq (.cv z) B)) p0004 p0006_e01_recanon
  have p0007_e02_recanon :
    Nominal.NPrf
      (.imp (.objEq x w) (syn_wb (syn_wa (.classMem (.cv x) A) (.classEq (.cv z) B))
          (syn_wa (.classMem (.cv w) A) (syn_wsb w x (.classEq (.cv z) B))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wa
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0006
  have p0007 :=
    @g_cbvopab1 (syn_wa (.classMem (.cv x) A) (.classEq (.cv z) B))
      (syn_wa (.classMem (.cv w) A) (syn_wsb w x (.classEq (.cv z) B))) x z w
      dv_cache_0004 dv_cache_0005 p0000 p0003 p0007_e02_recanon
  have p0008 := @g_nfv (.classMem (.cv w) A) y dv_cache_0006
  have p0009 := @g_nfeq2 y (.cv z) B dv_cache_0007 hyp_cbvmpt_1
  have p0010 := @g_nfsb (.classEq (.cv z) B) x w y dv_cache_0008 p0009
  have p0011 :=
    @g_nfan (.classMem (.cv w) A) (syn_wsb w x (.classEq (.cv z) B)) y p0008 p0010
  have p0012 := @g_nfv (syn_wa (.classMem (.cv y) A) (.classEq (.cv z) C)) w dv_cache_0009
  have p0013 := @g_eleq1 (.cv w) (.cv y) A
  have p0014 := @g_sbequ (.classEq (.cv z) B) w y x
  have p0015 := @g_nfeq2 x (.cv z) C dv_cache_0010 hyp_cbvmpt_2
  have p0016_e00_recanon :
    Nominal.NPrf (.imp (.classEq (.cv x) (.cv y)) (.classEq B C)) :=
    Nominal.RecanonTransportDev.transport
      (by
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      hyp_cbvmpt_3
  have p0016 := @g_eqeq2d (.classEq (.cv x) (.cv y)) B C (.cv z) p0016_e00_recanon
  have p0017_e01_recanon :
    Nominal.NPrf (.imp (.objEq x y) (syn_wb (.classEq (.cv z) B) (.classEq (.cv z) C))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0016
  have p0017 :=
    @g_sbie (.classEq (.cv z) B) (.classEq (.cv z) C) x y p0015 p0017_e01_recanon
  have p0018_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv w) (.cv y))
        (syn_wb (syn_wsb w x (.classEq (.cv z) B)) (syn_wsb y x (.classEq (.cv z) B)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wsb syn_wa syn_wex
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0014
  have p0018 :=
    @g_syl6bb (.classEq (.cv w) (.cv y)) (syn_wsb w x (.classEq (.cv z) B))
      (syn_wsb y x (.classEq (.cv z) B)) (.classEq (.cv z) C) p0018_e00_recanon p0017
  have p0019 :=
    @g_anbi12d (.classEq (.cv w) (.cv y)) (.classMem (.cv w) A) (.classMem (.cv y) A)
      (syn_wsb w x (.classEq (.cv z) B)) (.classEq (.cv z) C) p0013 p0018
  have p0020_e02_recanon :
    Nominal.NPrf
      (.imp (.objEq w y)
        (syn_wb (syn_wa (.classMem (.cv w) A) (syn_wsb w x (.classEq (.cv z) B)))
          (syn_wa (.classMem (.cv y) A) (.classEq (.cv z) C)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wa syn_wsb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0019
  have p0020 :=
    @g_cbvopab1 (syn_wa (.classMem (.cv w) A) (syn_wsb w x (.classEq (.cv z) B)))
      (syn_wa (.classMem (.cv y) A) (.classEq (.cv z) C)) w z y dv_cache_0011
      dv_cache_0012 p0011 p0012 p0020_e02_recanon
  have p0021 :=
    @g_eqtri (syn_copab x z (syn_wa (.classMem (.cv x) A) (.classEq (.cv z) B)))
      (syn_copab w z (syn_wa (.classMem (.cv w) A) (syn_wsb w x (.classEq (.cv z) B))))
      (syn_copab y z (syn_wa (.classMem (.cv y) A) (.classEq (.cv z) C))) p0007 p0020
  have p0022 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_mpt x z A B
      dv_cache_0013 dv_cache_0014 dv_cache_0004
  have p0023 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_mpt y z A C
      dv_cache_0013 dv_cache_0015 dv_cache_0016
  have p0024 :=
    @g_n_3eqtr4i (syn_copab x z (syn_wa (.classMem (.cv x) A) (.classEq (.cv z) B)))
      (syn_copab y z (syn_wa (.classMem (.cv y) A) (.classEq (.cv z) C))) (syn_cmpt x A B)
      (syn_cmpt y A C) p0021 p0022 p0023
  exact p0024

@[expose]
noncomputable def g_cbvmptv (x : Var) (y : Var) (A : Class) (B : Class) (C : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_y : y ∉ B.fv) (dv_C_x : x ∉ C.fv)
    (hyp_cbvmptv_1 : Nominal.NPrf (.imp (.objEq x y) (.classEq B C))) :
    Nominal.NPrf (.classEq (syn_cmpt x A B) (syn_cmpt y A C)) :=
  by
  have dv_cache_0001 : y ∉ (B).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_y, not_false_eq_true])
  have dv_cache_0002 : x ∉ (C).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_x, not_false_eq_true])
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
  have dv_cache_0004 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_y, not_false_eq_true])
  have p0000 := @g_nfcv y B dv_cache_0001
  have p0001 := @g_nfcv x C dv_cache_0002
  have p0002 := @g_cbvmpt x y A B C dv_cache_0003 dv_cache_0004 p0000 p0001 hyp_cbvmptv_1
  exact p0002

@[expose]
noncomputable def g_mptpreima (x : Var) (A : Class) (B : Class) (C : Class) (F : Class)
    (dv_C_x : x ∉ C.fv) (hyp_dmmpt2_1 : Nominal.NPrf (.classEq F (syn_cmpt x A B))) :
    Nominal.NPrf (.classEq (syn_cima (syn_ccnv F) C) (syn_crab x A (.classMem B C))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv ∪ F.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have dv_cache_0001 : y ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
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
  have dv_cache_0003 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0004 : y ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_C, not_false_eq_true])
  have dv_cache_0005 : x ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_x, not_false_eq_true])
  have dv_cache_0006 : y ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show y ≠ x from (by exact fresh_y_ne_x))
  have dv_cache_0007 : y ∉ ((Wff.classMem (.cv x) A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_x, fresh_y_not_A, or_false, not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_mpt x y A B
      dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    @g_eqtri F (syn_cmpt x A B)
      (syn_copab x y (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B))) hyp_dmmpt2_1
      p0000
  have p0002 :=
    @g_cnveqi F (syn_copab x y (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B))) p0001
  have p0003 :=
    @g_cnvopab (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B)) x y dv_cache_0003
  have p0004 :=
    @g_eqtri (syn_ccnv F)
      (syn_ccnv (syn_copab x y (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B))))
      (syn_copab y x (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B))) p0002 p0003
  have p0005 :=
    @g_imaeq1i (syn_ccnv F)
      (syn_copab y x (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B))) C p0004
  have p0006 :=
    @g_dfima3 (syn_copab y x (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B))) C
  have p0007 :=
    @g_resopab (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B)) y x C dv_cache_0004
      dv_cache_0005 dv_cache_0006
  have p0008 :=
    @g_rneqi
      (syn_cres (syn_copab y x (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B))) C)
      (syn_copab y x (syn_wa (.classMem (.cv y) C)
          (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B))))
      p0007
  have p0009 :=
    @g_ancom (.classMem (.cv y) C) (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B))
  have p0010 := @g_anass (.classMem (.cv x) A) (.classEq (.cv y) B) (.classMem (.cv y) C)
  have p0011 :=
    @g_bitri
      (syn_wa (.classMem (.cv y) C) (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B)))
      (syn_wa (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B)) (.classMem (.cv y) C))
      (syn_wa (.classMem (.cv x) A) (syn_wa (.classEq (.cv y) B) (.classMem (.cv y) C)))
      p0009 p0010
  have p0012 :=
    @g_exbii
      (syn_wa (.classMem (.cv y) C) (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B)))
      (syn_wa (.classMem (.cv x) A) (syn_wa (.classEq (.cv y) B) (.classMem (.cv y) C))) y
      p0011
  have p0013 :=
    @g_n_19_42v (.classMem (.cv x) A) (syn_wa (.classEq (.cv y) B) (.classMem (.cv y) C))
      y dv_cache_0007
  have p0014 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClelOfDV y B C
      dv_cache_0002 dv_cache_0004)
  have p0015 :=
    @g_bicomi (.classMem B C)
      (syn_wex y (syn_wa (.classEq (.cv y) B) (.classMem (.cv y) C))) p0014
  have p0016 :=
    @g_anbi2i (syn_wex y (syn_wa (.classEq (.cv y) B) (.classMem (.cv y) C)))
      (.classMem B C) (.classMem (.cv x) A) p0015
  have p0017 :=
    @g_bitri
      (syn_wex y (syn_wa (.classMem (.cv x) A)
          (syn_wa (.classEq (.cv y) B) (.classMem (.cv y) C))))
      (syn_wa (.classMem (.cv x) A)
        (syn_wex y (syn_wa (.classEq (.cv y) B) (.classMem (.cv y) C))))
      (syn_wa (.classMem (.cv x) A) (.classMem B C)) p0013 p0016
  have p0018 :=
    @g_bitri
      (syn_wex y (syn_wa (.classMem (.cv y) C)
          (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B))))
      (syn_wex y (syn_wa (.classMem (.cv x) A)
          (syn_wa (.classEq (.cv y) B) (.classMem (.cv y) C))))
      (syn_wa (.classMem (.cv x) A) (.classMem B C)) p0012 p0017
  have p0019 :=
    @g_abbii
      (syn_wex y (syn_wa (.classMem (.cv y) C)
          (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B))))
      (syn_wa (.classMem (.cv x) A) (.classMem B C)) x p0018
  have p0020 :=
    @g_rnopab
      (syn_wa (.classMem (.cv y) C) (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B))) y
      x dv_cache_0006
  have p0021 := (Nominal.classEqRefl (syn_crab x A (.classMem B C)))
  have p0022 :=
    @g_n_3eqtr4i
      (.cab x (syn_wex y (syn_wa (.classMem (.cv y) C)
            (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B)))))
      (.cab x (syn_wa (.classMem (.cv x) A) (.classMem B C)))
      (syn_crn (syn_copab y x (syn_wa (.classMem (.cv y) C)
            (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B)))))
      (syn_crab x A (.classMem B C)) p0019 p0020 p0021
  have p0023 :=
    @g_eqtri
      (syn_crn (syn_cres (syn_copab y x (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B))) C))
      (syn_crn (syn_copab y x (syn_wa (.classMem (.cv y) C)
            (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B)))))
      (syn_crab x A (.classMem B C)) p0008 p0022
  have p0024 :=
    @g_eqtri
      (syn_cima (syn_copab y x (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B))) C)
      (syn_crn (syn_cres (syn_copab y x (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B))) C))
      (syn_crab x A (.classMem B C)) p0006 p0023
  have p0025 :=
    @g_eqtri (syn_cima (syn_ccnv F) C)
      (syn_cima (syn_copab y x (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B))) C)
      (syn_crab x A (.classMem B C)) p0005 p0024
  exact p0025

@[expose]
noncomputable def g_dmmpt (x : Var) (A : Class) (B : Class) (F : Class)
    (hyp_dmmpt2_1 : Nominal.NPrf (.classEq F (syn_cmpt x A B))) :
    Nominal.NPrf (.classEq (syn_cdm F) (syn_crab x A (.classMem B (syn_cvv)))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv ∪ F.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have dv_cache_0001 : y ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
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
  have dv_cache_0003 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0004 : y ∉ ((Wff.classMem (.cv x) A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_x, fresh_y_not_A, or_false, not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_mpt x y A B
      dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    @g_eqtri F (syn_cmpt x A B)
      (syn_copab x y (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B))) hyp_dmmpt2_1
      p0000
  have p0002 :=
    @g_dmeqi F (syn_copab x y (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B))) p0001
  have p0003 :=
    @g_dmopab (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B)) x y dv_cache_0003
  have p0004 := @g_n_19_42v (.classMem (.cv x) A) (.classEq (.cv y) B) y dv_cache_0004
  have p0005 := @g_isset y B dv_cache_0002
  have p0006 :=
    @g_anbi2i (.classMem B (syn_cvv)) (syn_wex y (.classEq (.cv y) B))
      (.classMem (.cv x) A) p0005
  have p0007 :=
    @g_bitr4i (syn_wex y (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B)))
      (syn_wa (.classMem (.cv x) A) (syn_wex y (.classEq (.cv y) B)))
      (syn_wa (.classMem (.cv x) A) (.classMem B (syn_cvv))) p0004 p0006
  have p0008 :=
    @g_abbii (syn_wex y (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B)))
      (syn_wa (.classMem (.cv x) A) (.classMem B (syn_cvv))) x p0007
  have p0009 := (Nominal.classEqRefl (syn_crab x A (.classMem B (syn_cvv))))
  have p0010 :=
    @g_eqtr4i (.cab x (syn_wex y (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B))))
      (.cab x (syn_wa (.classMem (.cv x) A) (.classMem B (syn_cvv))))
      (syn_crab x A (.classMem B (syn_cvv))) p0008 p0009
  have p0011 :=
    @g_n_3eqtri (syn_cdm F)
      (syn_cdm (syn_copab x y (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B))))
      (.cab x (syn_wex y (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B))))
      (syn_crab x A (.classMem B (syn_cvv))) p0002 p0003 p0010
  exact p0011

@[expose]
noncomputable def g_rnmpt (x : Var) (y : Var) (A : Class) (B : Class) (F : Class)
    (dv_A_y : y ∉ A.fv) (dv_B_y : y ∉ B.fv) (dv_x_y : x ≠ y)
    (hyp_rnmpt_1 : Nominal.NPrf (.classEq F (syn_cmpt x A B))) :
    Nominal.NPrf (.classEq (syn_crn F) (.cab y (syn_wrex x A (.classEq (.cv y) B)))) :=
  by
  have dv_cache_0001 : y ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_y, not_false_eq_true])
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
  have dv_cache_0003 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show x ≠ y from (by exact dv_x_y))
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_mpt x y A B
      dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    @g_eqtri F (syn_cmpt x A B)
      (syn_copab x y (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B))) hyp_rnmpt_1
      p0000
  have p0002 :=
    @g_rneqi F (syn_copab x y (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B))) p0001
  have p0003 := @g_rnopab2 x y A B dv_cache_0003
  have p0004 :=
    @g_eqtri (syn_crn F)
      (syn_crn (syn_copab x y (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B))))
      (.cab y (syn_wrex x A (.classEq (.cv y) B))) p0002 p0003
  exact p0004

@[expose]
noncomputable def g_mptfng (x : Var) (A : Class) (B : Class) (F : Class)
    (dv_A_x : x ∉ A.fv) (hyp_mptfng_1 : Nominal.NPrf (.classEq F (syn_cmpt x A B))) :
    Nominal.NPrf (syn_wb (syn_wral x A (.classMem B (syn_cvv))) (syn_wfn F A)) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv ∪ F.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have dv_cache_0001 : y ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
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
  have dv_cache_0003 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0004 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_mpt x y A B
      dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    @g_eqtri F (syn_cmpt x A B)
      (syn_copab x y (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B))) hyp_mptfng_1
      p0000
  have p0002 :=
    @g_fnopab2g x y A B F dv_cache_0004 dv_cache_0001 dv_cache_0002 dv_cache_0003 p0001
  exact p0002

@[expose]
noncomputable def g_fnmpt (x : Var) (A : Class) (B : Class) (F : Class) (V : Class)
    (dv_A_x : x ∉ A.fv) (hyp_mptfng_1 : Nominal.NPrf (.classEq F (syn_cmpt x A B))) :
    Nominal.NPrf (.imp (syn_wral x A (.classMem B V)) (syn_wfn F A)) :=
  by
  have dv_cache_0001 : x ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have p0000 := @g_elex B V
  have p0001 := @g_ralimi (.classMem B V) (.classMem B (syn_cvv)) x A p0000
  have p0002 := @g_mptfng x A B F dv_cache_0001 hyp_mptfng_1
  have p0003 :=
    @g_sylib (syn_wral x A (.classMem B V)) (syn_wral x A (.classMem B (syn_cvv)))
      (syn_wfn F A) p0001 p0002
  exact p0003

@[expose]
noncomputable def g_fnmpti (x : Var) (A : Class) (B : Class) (F : Class)
    (dv_A_x : x ∉ A.fv) (hyp_fnmpti_1 : Nominal.NPrf (.classMem B (syn_cvv)))
    (hyp_fnmpti_2 : Nominal.NPrf (.classEq F (syn_cmpt x A B))) :
    Nominal.NPrf (syn_wfn F A) :=
  by
  have dv_cache_0001 : x ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have p0000 := @g_rgenw (.classMem B (syn_cvv)) x A hyp_fnmpti_1
  have p0001 := @g_mptfng x A B F dv_cache_0001 hyp_fnmpti_2
  have p0002 := @g_mpbi (syn_wral x A (.classMem B (syn_cvv))) (syn_wfn F A) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_fmpt (x : Var) (A : Class) (B : Class) (C : Class) (F : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv)
    (hyp_fmpt_1 : Nominal.NPrf (.classEq F (syn_cmpt x A C))) :
    Nominal.NPrf (syn_wb (syn_wral x A (.classMem C B)) (syn_wf F A B)) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv ∪ F.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
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
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0003 : y ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_C, not_false_eq_true])
  have dv_cache_0004 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0005 : x ∉ ((Wff.classMem (.cv y) B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_y, dv_B_x, or_false, not_false_eq_true])
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
  have dv_cache_0007 : y ∉ ((syn_wral x A (.classMem C B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union,
          Finset.mem_erase, fresh_y_not_A, fresh_y_not_C, fresh_y_not_B, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0008 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_x, not_false_eq_true])
  have p0000 := @g_fnmpt x A C F B dv_cache_0001 hyp_fmpt_1
  have p0001 := @g_rnmpt x y A C F dv_cache_0002 dv_cache_0003 dv_cache_0004 hyp_fmpt_1
  have p0002 := @g_r19_29 (.classMem C B) (.classEq (.cv y) C) x A
  have p0003 := @g_eleq1 (.cv y) C B
  have p0004 :=
    @g_biimparc (.classEq (.cv y) C) (.classMem (.cv y) B) (.classMem C B) p0003
  have p0005 :=
    @g_rexlimivw (syn_wa (.classMem C B) (.classEq (.cv y) C)) (.classMem (.cv y) B) x A
      dv_cache_0005 p0004
  have p0006 :=
    @g_syl (syn_wa (syn_wral x A (.classMem C B)) (syn_wrex x A (.classEq (.cv y) C)))
      (syn_wrex x A (syn_wa (.classMem C B) (.classEq (.cv y) C))) (.classMem (.cv y) B)
      p0002 p0005
  have p0007 :=
    @g_ex (syn_wral x A (.classMem C B)) (syn_wrex x A (.classEq (.cv y) C))
      (.classMem (.cv y) B) p0006
  have p0008 :=
    @g_abssdv (syn_wral x A (.classMem C B)) (syn_wrex x A (.classEq (.cv y) C)) y B
      dv_cache_0006 dv_cache_0007 p0007
  have p0009 :=
    @g_syl5eqss (syn_wral x A (.classMem C B)) (syn_crn F)
      (.cab y (syn_wrex x A (.classEq (.cv y) C))) B p0001 p0008
  have p0010 := (Nominal.biimpRefl (syn_wf F A B))
  have p0011 :=
    @g_sylanbrc (syn_wral x A (.classMem C B)) (syn_wfn F A) (syn_wss (syn_crn F) B)
      (syn_wf F A B) p0000 p0009 p0010
  have p0012 := @g_mptpreima x A C B F dv_cache_0008 hyp_fmpt_1
  have p0013 := @g_fimacnv A B F
  have p0014 :=
    @g_syl5reqr (syn_wf F A B) (syn_crab x A (.classMem C B)) (syn_cima (syn_ccnv F) B) A
      p0012 p0013
  have p0015 := @g_rabid2 (.classMem C B) x A dv_cache_0001
  have p0016 :=
    @g_sylib (syn_wf F A B) (.classEq A (syn_crab x A (.classMem C B)))
      (syn_wral x A (.classMem C B)) p0014 p0015
  have p0017 := @g_impbii (syn_wral x A (.classMem C B)) (syn_wf F A B) p0011 p0016
  exact p0017

@[expose]
noncomputable def g_fmpti (x : Var) (A : Class) (B : Class) (C : Class) (F : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv)
    (hyp_fmpt_1 : Nominal.NPrf (.classEq F (syn_cmpt x A C)))
    (hyp_fmpti_2 : Nominal.NPrf (.imp (.classMem (.cv x) A) (.classMem C B))) :
    Nominal.NPrf (syn_wf F A B) :=
  by
  have dv_cache_0001 : x ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have dv_cache_0002 : x ∉ (B).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_x, not_false_eq_true])
  have p0000 := @g_rgen (.classMem C B) x A hyp_fmpti_2
  have p0001 := @g_fmpt x A B C F dv_cache_0001 dv_cache_0002 hyp_fmpt_1
  have p0002 := @g_mpbi (syn_wral x A (.classMem C B)) (syn_wf F A B) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_resmpt (x : Var) (A : Class) (B : Class) (C : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf
      (.imp (syn_wss B A) (.classEq (syn_cres (syn_cmpt x A C) B) (syn_cmpt x B C))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ (B).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_x, not_false_eq_true])
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
  have dv_cache_0005 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0006 : y ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_C, not_false_eq_true])
  have p0000 :=
    @g_resopab2 (.classEq (.cv y) C) x y B A dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005
  have p0001 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_mpt x y A C
      dv_cache_0004 dv_cache_0006 dv_cache_0005
  have p0002 :=
    @g_reseq1i (syn_cmpt x A C)
      (syn_copab x y (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) C))) B p0001
  have p0003 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_mpt x y B C
      dv_cache_0002 dv_cache_0006 dv_cache_0005
  have p0004 :=
    @g_n_3eqtr4g (syn_wss B A)
      (syn_cres (syn_copab x y (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) C))) B)
      (syn_copab x y (syn_wa (.classMem (.cv x) B) (.classEq (.cv y) C)))
      (syn_cres (syn_cmpt x A C) B) (syn_cmpt x B C) p0000 p0002 p0003
  exact p0004

@[expose]
noncomputable def g_fvmptg (x : Var) (A : Class) (B : Class) (C : Class) (D : Class)
    (R : Class) (F : Class) (dv_A_x : x ∉ A.fv) (dv_C_x : x ∉ C.fv) (dv_D_x : x ∉ D.fv)
    (hyp_fvmptg_1 : Nominal.NPrf (.imp (.classEq (.cv x) A) (.classEq B C)))
    (hyp_fvmptg_2 : Nominal.NPrf (.classEq F (syn_cmpt x D B))) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A D) (.classMem C R)) (.classEq (syn_cfv F A) C)) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv ∪ D.fv ∪ R.fv ∪ F.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))))
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_y_not_D : y ∉ D.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have dv_cache_0001 : y ∉ (D).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_D, not_false_eq_true])
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
  have dv_cache_0003 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0004 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have dv_cache_0005 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0006 : x ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_x, not_false_eq_true])
  have dv_cache_0007 : y ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_C, not_false_eq_true])
  have dv_cache_0008 : x ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_D_x, not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_mpt x y D B
      dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    @g_eqtri F (syn_cmpt x D B)
      (syn_copab x y (syn_wa (.classMem (.cv x) D) (.classEq (.cv y) B))) hyp_fvmptg_2
      p0000
  have p0002 :=
    @g_fvopab4g x y A B C D R F dv_cache_0004 dv_cache_0005 dv_cache_0002 dv_cache_0006
      dv_cache_0007 dv_cache_0008 dv_cache_0001 dv_cache_0003 hyp_fvmptg_1 p0001
  exact p0002


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk012BCompact001Part016`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_fvmpti (x : Var) (A : Class) (B : Class) (C : Class) (D : Class)
    (F : Class) (dv_A_x : x ∉ A.fv) (dv_C_x : x ∉ C.fv) (dv_D_x : x ∉ D.fv)
    (hyp_fvmptg_1 : Nominal.NPrf (.imp (.classEq (.cv x) A) (.classEq B C)))
    (hyp_fvmptg_2 : Nominal.NPrf (.classEq F (syn_cmpt x D B))) :
    Nominal.NPrf (.imp (.classMem A D) (.classEq (syn_cfv F A) (syn_cfv (syn_cid) C))) :=
  by
  have dv_cache_0001 : x ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have dv_cache_0002 : x ∉ (C).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_x, not_false_eq_true])
  have dv_cache_0003 : x ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_D_x, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((Wff.classMem C (syn_cvv))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, dv_C_x,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 :=
    @g_fvmptg x A B C D (syn_cvv) F dv_cache_0001 dv_cache_0002 dv_cache_0003 hyp_fvmptg_1
      hyp_fvmptg_2
  have p0001 := @g_fvi C (syn_cvv)
  have p0002 :=
    @g_adantl (.classMem C (syn_cvv)) (.classEq (syn_cfv (syn_cid) C) C) (.classMem A D)
      p0001
  have p0003 :=
    @g_eqtr4d (syn_wa (.classMem A D) (.classMem C (syn_cvv))) (syn_cfv F A) C
      (syn_cfv (syn_cid) C) p0000 p0002
  have p0004 := @g_eleq1d (.classEq (.cv x) A) B C (syn_cvv) hyp_fvmptg_1
  have p0005 := @g_dmmpt x D B F hyp_fvmptg_2
  have p0006 :=
    @g_elrab2 (.classMem B (syn_cvv)) (.classMem C (syn_cvv)) x A D (syn_cdm F)
      dv_cache_0001 dv_cache_0003 dv_cache_0004 p0004 p0005
  have p0007 :=
    @g_baib (.classMem A (syn_cdm F)) (.classMem A D) (.classMem C (syn_cvv)) p0006
  have p0008 :=
    @g_notbid (.classMem A D) (.classMem A (syn_cdm F)) (.classMem C (syn_cvv)) p0007
  have p0009 := @g_ndmfv A F
  have p0010 :=
    @g_syl6bir (.classMem A D) (.neg (.classMem C (syn_cvv)))
      (.neg (.classMem A (syn_cdm F))) (.classEq (syn_cfv F A) (syn_c0)) p0008 p0009
  have p0011 :=
    @g_imp (.classMem A D) (.neg (.classMem C (syn_cvv)))
      (.classEq (syn_cfv F A) (syn_c0)) p0010
  have p0012 := @g_fvprc C (syn_cid)
  have p0013 :=
    @g_adantl (.neg (.classMem C (syn_cvv))) (.classEq (syn_cfv (syn_cid) C) (syn_c0))
      (.classMem A D) p0012
  have p0014 :=
    @g_eqtr4d (syn_wa (.classMem A D) (.neg (.classMem C (syn_cvv)))) (syn_cfv F A)
      (syn_c0) (syn_cfv (syn_cid) C) p0011 p0013
  have p0015 :=
    @g_pm2_61dan (.classMem A D) (.classMem C (syn_cvv))
      (.classEq (syn_cfv F A) (syn_cfv (syn_cid) C)) p0003 p0014
  exact p0015

@[expose]
noncomputable def g_fvmpt (x : Var) (A : Class) (B : Class) (C : Class) (D : Class)
    (F : Class) (dv_A_x : x ∉ A.fv) (dv_C_x : x ∉ C.fv) (dv_D_x : x ∉ D.fv)
    (hyp_fvmptg_1 : Nominal.NPrf (.imp (.classEq (.cv x) A) (.classEq B C)))
    (hyp_fvmptg_2 : Nominal.NPrf (.classEq F (syn_cmpt x D B)))
    (hyp_fvmpt_3 : Nominal.NPrf (.classMem C (syn_cvv))) :
    Nominal.NPrf (.imp (.classMem A D) (.classEq (syn_cfv F A) C)) :=
  by
  have dv_cache_0001 : x ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have dv_cache_0002 : x ∉ (C).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_x, not_false_eq_true])
  have dv_cache_0003 : x ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_D_x, not_false_eq_true])
  have p0000 :=
    @g_fvmptg x A B C D (syn_cvv) F dv_cache_0001 dv_cache_0002 dv_cache_0003 hyp_fvmptg_1
      hyp_fvmptg_2
  have p0001 :=
    @g_mpan2 (.classMem A D) (.classMem C (syn_cvv)) (.classEq (syn_cfv F A) C)
      hyp_fvmpt_3 p0000
  exact p0001

@[expose]
noncomputable def g_fvmpts (x : Var) (A : Class) (B : Class) (C : Class) (F : Class)
    (V : Class) (dv_C_x : x ∉ C.fv)
    (hyp_fvmpts_1 : Nominal.NPrf (.classEq F (syn_cmpt x C B))) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A C) (.classMem (syn_csb A x B) V))
        (.classEq (syn_cfv F A) (syn_csb A x B))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv ∪ F.fv ∪ V.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have dv_cache_0001 : y ∉ (B).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_B, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_y, not_false_eq_true])
  have dv_cache_0003 : x ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_x, not_false_eq_true])
  have dv_cache_0004 : y ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_C, not_false_eq_true])
  have dv_cache_0005 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0006 : y ∉ ((syn_csb A x B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csb, Finset.mem_union,
          Finset.mem_erase, fresh_y_not_A, fresh_y_not_B, or_false, and_false,
          not_false_eq_true])
  have p0000 := @g_csbeq1 x (.cv y) A B
  have p0001 := @g_nfcv y B dv_cache_0001
  have p0002 := @g_nfcsb1v x (.cv y) B dv_cache_0002
  have p0003 := @g_csbeq1a x (.cv y) B
  have p0004_e02_recanon :
    Nominal.NPrf (.imp (.objEq x y) (.classEq B (syn_csb (.cv y) x B))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_csb syn_wsbc
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0003
  have p0004 :=
    @g_cbvmpt x y C B (syn_csb (.cv y) x B) dv_cache_0003 dv_cache_0004 p0001 p0002
      p0004_e02_recanon
  have p0005 :=
    @g_eqtri F (syn_cmpt x C B) (syn_cmpt y C (syn_csb (.cv y) x B)) hyp_fvmpts_1 p0004
  have p0006 :=
    @g_fvmptg y A (syn_csb (.cv y) x B) (syn_csb A x B) C V F dv_cache_0005 dv_cache_0006
      dv_cache_0004 p0000 p0005
  exact p0006

@[expose]
noncomputable def g_fvmptd (ph : Wff) (x : Var) (A : Class) (B : Class) (C : Class)
    (D : Class) (F : Class) (V : Class) (dv_A_x : x ∉ A.fv) (dv_C_x : x ∉ C.fv)
    (dv_D_x : x ∉ D.fv) (dv_ph_x : x ∉ ph.fv)
    (hyp_fvmptd_1 : Nominal.NPrf (.imp ph (.classEq F (syn_cmpt x D B))))
    (hyp_fvmptd_2 : Nominal.NPrf (.imp (syn_wa ph (.classEq (.cv x) A)) (.classEq B C)))
    (hyp_fvmptd_3 : Nominal.NPrf (.imp ph (.classMem A D)))
    (hyp_fvmptd_4 : Nominal.NPrf (.imp ph (.classMem C V))) :
    Nominal.NPrf (.imp ph (.classEq (syn_cfv F A) C)) :=
  by
  have dv_cache_0001 : x ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have dv_cache_0002 : x ∉ (C).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_x, not_false_eq_true])
  have dv_cache_0003 : x ∉ (ph).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_ph_x, not_false_eq_true])
  have dv_cache_0004 : x ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_D_x, not_false_eq_true])
  have p0000 := @g_fveq1d ph A F (syn_cmpt x D B) hyp_fvmptd_1
  have p0001 :=
    @g_csbied ph x A B C D dv_cache_0001 dv_cache_0002 dv_cache_0003 hyp_fvmptd_3
      hyp_fvmptd_2
  have p0002 := @g_eqeltrd ph (syn_csb A x B) C V p0001 hyp_fvmptd_4
  have p0003 := @g_eqid (syn_cmpt x D B)
  have p0004 := @g_fvmpts x A B D (syn_cmpt x D B) V dv_cache_0004 p0003
  have p0005 :=
    @g_syl2anc ph (.classMem A D) (.classMem (syn_csb A x B) V)
      (.classEq (syn_cfv (syn_cmpt x D B) A) (syn_csb A x B)) hyp_fvmptd_3 p0002 p0004
  have p0006 :=
    @g_n_3eqtrd ph (syn_cfv F A) (syn_cfv (syn_cmpt x D B) A) (syn_csb A x B) C p0000
      p0005 p0001
  exact p0006

@[expose]
noncomputable def g_fvmpt2i (x : Var) (A : Class) (B : Class) (F : Class)
    (dv_A_x : x ∉ A.fv) (hyp_fvmpt2_1 : Nominal.NPrf (.classEq F (syn_cmpt x A B))) :
    Nominal.NPrf
      (.imp (.classMem (.cv x) A) (.classEq (syn_cfv F (.cv x)) (syn_cfv (syn_cid) B))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv ∪ F.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have dv_cache_0001 : y ∉ (B).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_B, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_y, not_false_eq_true])
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
  have dv_cache_0005 : y ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_x, not_false_eq_true])
  have p0000 := @g_csbeq1 x (.cv y) (.cv x) B
  have p0001 := @g_csbid x B
  have p0002 :=
    @g_syl6eq (.classEq (.cv y) (.cv x)) (syn_csb (.cv y) x B) (syn_csb (.cv x) x B) B
      p0000 p0001
  have p0003 := @g_nfcv y B dv_cache_0001
  have p0004 := @g_nfcsb1v x (.cv y) B dv_cache_0002
  have p0005 := @g_csbeq1a x (.cv y) B
  have p0006_e02_recanon :
    Nominal.NPrf (.imp (.objEq x y) (.classEq B (syn_csb (.cv y) x B))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_csb syn_wsbc
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0005
  have p0006 :=
    @g_cbvmpt x y A B (syn_csb (.cv y) x B) dv_cache_0003 dv_cache_0004 p0003 p0004
      p0006_e02_recanon
  have p0007 :=
    @g_eqtri F (syn_cmpt x A B) (syn_cmpt y A (syn_csb (.cv y) x B)) hyp_fvmpt2_1 p0006
  have p0008 :=
    @g_fvmpti y (.cv x) (syn_csb (.cv y) x B) B A F dv_cache_0005 dv_cache_0001
      dv_cache_0004 p0002 p0007
  exact p0008

@[expose]
noncomputable def g_fvmpt2 (x : Var) (A : Class) (B : Class) (C : Class) (F : Class)
    (dv_A_x : x ∉ A.fv) (hyp_fvmpt2_1 : Nominal.NPrf (.classEq F (syn_cmpt x A B))) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem (.cv x) A) (.classMem B C)) (.classEq (syn_cfv F (.cv x)) B)) :=
  by
  have dv_cache_0001 : x ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have p0000 := @g_fvmpt2i x A B F dv_cache_0001 hyp_fvmpt2_1
  have p0001 := @g_fvi B C
  have p0002 :=
    @g_sylan9eq (.classMem (.cv x) A) (.classMem B C) (syn_cfv F (.cv x))
      (syn_cfv (syn_cid) B) B p0000 p0001
  exact p0002

@[expose]
noncomputable def g_mpt2mptx (x : Var) (y : Var) (z : Var) (A : Class) (B : Class)
    (C : Class) (D : Class) (_dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv)
    (dv_B_y : y ∉ B.fv) (dv_B_z : z ∉ B.fv) (dv_C_x : x ∉ C.fv) (dv_C_y : y ∉ C.fv)
    (dv_D_z : z ∉ D.fv) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z)
    (hyp_mpt2mpt_1 :
      Nominal.NPrf (.imp (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) (.classEq C D))) :
    Nominal.NPrf
      (.classEq (syn_cmpt z (syn_ciun x A (syn_cxp (syn_csn (.cv x)) B)) C)
        (syn_cmpt2 x A y B D)) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var) ∪ A.fv ∪ B.fv ∪
        C.fv ∪
      D.fv
  let w : Var := freshVar proofSupport 0
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))))
  have fresh_x_ne_w : x ≠ w := Ne.symm fresh_w_ne_x
  have fresh_w_ne_y : w ≠ y := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))
  have fresh_y_ne_w : y ≠ w := Ne.symm fresh_w_ne_y
  have fresh_w_ne_z : w ≠ z := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_z_ne_w : z ≠ w := Ne.symm fresh_w_ne_z
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_w_not_B : w ∉ B.fv := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_w_not_C : w ∉ C.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_w_not_D : w ∉ D.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have dv_cache_0001 : w ∉ ((syn_ciun x A (syn_cxp (syn_csn (.cv x)) B))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ciun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_w_not_A, fresh_w_ne_x, fresh_w_not_B, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0002 : w ∉ (C).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_C, not_false_eq_true])
  have dv_cache_0003 : z ≠ w :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show z ≠ w from (by exact fresh_z_ne_w))
  have dv_cache_0004 : w ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_A, not_false_eq_true])
  have dv_cache_0005 : w ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_B, not_false_eq_true])
  have dv_cache_0006 : w ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_D, not_false_eq_true])
  have dv_cache_0007 : x ≠ w :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show x ≠ w from (by exact fresh_x_ne_w))
  have dv_cache_0008 : y ≠ w :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show y ≠ w from (by exact fresh_y_ne_w))
  have dv_cache_0009 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_y, not_false_eq_true])
  have dv_cache_0010 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_y, not_false_eq_true])
  have dv_cache_0011 : x ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, dv_x_z,
          not_false_eq_true])
  have dv_cache_0012 : y ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, dv_y_z,
          not_false_eq_true])
  have dv_cache_0013 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0014 : x ∉ ((Wff.classEq (.cv w) C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_w, dv_C_x, or_false, not_false_eq_true])
  have dv_cache_0015 : y ∉ ((Wff.classEq (.cv w) C)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_w, dv_C_y, or_false, not_false_eq_true])
  have dv_cache_0016 :
    z ∉
      ((syn_wa (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)) (.classEq (.cv w) D))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_x_z), dv_A_z, (Ne.symm dv_y_z), dv_B_z,
          fresh_z_ne_w, dv_D_z, or_false, not_false_eq_true])
  have dv_cache_0017 : z ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (show z ≠ x from (by exact Ne.symm dv_x_z))
  have dv_cache_0018 : z ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (show z ≠ y from (by exact Ne.symm dv_y_z))
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_mpt z w
      (syn_ciun x A (syn_cxp (syn_csn (.cv x)) B)) C dv_cache_0001 dv_cache_0002
      dv_cache_0003
  have p0001 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_mpt2 x y w A B D
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
  have p0002 :=
    @g_eliunxp x y A B (.cv z) dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
      dv_cache_0013
  have p0003 :=
    @g_anbi1i (.classMem (.cv z) (syn_ciun x A (syn_cxp (syn_csn (.cv x)) B)))
      (syn_wex x (syn_wex y (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y)))
            (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)))))
      (.classEq (.cv w) C) p0002
  have p0004 :=
    @g_n_19_41vv
      (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y)))
        (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)))
      (.classEq (.cv w) C) x y dv_cache_0014 dv_cache_0015
  have p0005 :=
    @g_anass (.classEq (.cv z) (syn_cop (.cv x) (.cv y)))
      (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)) (.classEq (.cv w) C)
  have p0006 :=
    @g_eqeq2d (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) C D (.cv w) hyp_mpt2mpt_1
  have p0007 :=
    @g_anbi2d (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) (.classEq (.cv w) C)
      (.classEq (.cv w) D) (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)) p0006
  have p0008 :=
    @g_pm5_32i (.classEq (.cv z) (syn_cop (.cv x) (.cv y)))
      (syn_wa (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)) (.classEq (.cv w) C))
      (syn_wa (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)) (.classEq (.cv w) D))
      p0007
  have p0009 :=
    @g_bitri
      (syn_wa (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y)))
          (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B))) (.classEq (.cv w) C))
      (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y)))
        (syn_wa (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)) (.classEq (.cv w) C)))
      (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y)))
        (syn_wa (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)) (.classEq (.cv w) D)))
      p0005 p0008
  have p0010 :=
    @g_n_2exbii
      (syn_wa (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y)))
          (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B))) (.classEq (.cv w) C))
      (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y)))
        (syn_wa (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)) (.classEq (.cv w) D)))
      x y p0009
  have p0011 :=
    @g_n_3bitr2i
      (syn_wa (.classMem (.cv z) (syn_ciun x A (syn_cxp (syn_csn (.cv x)) B)))
        (.classEq (.cv w) C))
      (syn_wa (syn_wex x (syn_wex y (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y)))
              (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B))))) (.classEq (.cv w) C))
      (syn_wex x (syn_wex y (syn_wa (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y)))
              (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B))) (.classEq (.cv w) C))))
      (syn_wex x (syn_wex y (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y)))
            (syn_wa (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B))
              (.classEq (.cv w) D)))))
      p0003 p0004 p0010
  have p0012 :=
    @g_opabbii
      (syn_wa (.classMem (.cv z) (syn_ciun x A (syn_cxp (syn_csn (.cv x)) B)))
        (.classEq (.cv w) C))
      (syn_wex x (syn_wex y (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y)))
            (syn_wa (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B))
              (.classEq (.cv w) D)))))
      z w p0011
  have p0013 :=
    @g_dfoprab2
      (syn_wa (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)) (.classEq (.cv w) D)) x
      y w z dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0003 dv_cache_0007
      dv_cache_0008
  have p0014 :=
    @g_eqtr4i
      (syn_copab z w (syn_wa (.classMem (.cv z) (syn_ciun x A (syn_cxp (syn_csn (.cv x)) B)))
          (.classEq (.cv w) C)))
      (syn_copab z w (syn_wex x (syn_wex y (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y)))
              (syn_wa (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B))
                (.classEq (.cv w) D))))))
      (syn_coprab x y w (syn_wa (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B))
          (.classEq (.cv w) D)))
      p0012 p0013
  have p0015 :=
    @g_eqtr4i (syn_cmpt2 x A y B D)
      (syn_coprab x y w (syn_wa (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B))
          (.classEq (.cv w) D)))
      (syn_copab z w (syn_wa (.classMem (.cv z) (syn_ciun x A (syn_cxp (syn_csn (.cv x)) B)))
          (.classEq (.cv w) C)))
      p0001 p0014
  have p0016 :=
    @g_eqtr4i (syn_cmpt z (syn_ciun x A (syn_cxp (syn_csn (.cv x)) B)) C)
      (syn_copab z w (syn_wa (.classMem (.cv z) (syn_ciun x A (syn_cxp (syn_csn (.cv x)) B)))
          (.classEq (.cv w) C)))
      (syn_cmpt2 x A y B D) p0000 p0015
  exact p0016

@[expose]
noncomputable def g_ovmpt2ga (x : Var) (y : Var) (A : Class) (B : Class) (C : Class)
    (D : Class) (R : Class) (S : Class) (F : Class) (H : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_C_x : x ∉ C.fv)
    (dv_C_y : y ∉ C.fv) (dv_D_x : x ∉ D.fv) (dv_D_y : y ∉ D.fv) (dv_S_x : x ∉ S.fv)
    (dv_S_y : y ∉ S.fv) (dv_x_y : x ≠ y)
    (hyp_ovmpt2ga_1 : Nominal.NPrf
        (.imp (syn_wa (.classEq (.cv x) A) (.classEq (.cv y) B)) (.classEq R S)))
    (hyp_ovmpt2ga_2 : Nominal.NPrf (.classEq F (syn_cmpt2 x C y D R))) :
    Nominal.NPrf
      (.imp (syn_w3a (.classMem A C) (.classMem B D) (.classMem S H))
        (.classEq (syn_co A F B) S)) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv ∪ D.fv ∪ R.fv ∪
          S.fv ∪
        F.fv ∪
      H.fv
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
                    (Finset.mem_union_left _ (Finset.mem_union_left _
                        (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))))))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
                    (Finset.mem_union_left _ (Finset.mem_union_left _
                        (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))))))
  have fresh_y_ne_z : y ≠ z := Ne.symm fresh_z_ne_y
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
                    (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))))))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))))
  have fresh_z_not_C : z ∉ C.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))))
  have fresh_z_not_D : z ∉ D.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_z_not_R : z ∉ R.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_z_not_S : z ∉ S.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have dv_cache_0001 : z ∉ (C).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_C, not_false_eq_true])
  have dv_cache_0002 : z ∉ (D).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_D, not_false_eq_true])
  have dv_cache_0003 : z ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_R, not_false_eq_true])
  have dv_cache_0004 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0005 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0006 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have dv_cache_0007 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_y, not_false_eq_true])
  have dv_cache_0008 : z ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_A, not_false_eq_true])
  have dv_cache_0009 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_x, not_false_eq_true])
  have dv_cache_0010 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_y, not_false_eq_true])
  have dv_cache_0011 : z ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_B, not_false_eq_true])
  have dv_cache_0012 : x ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_x, not_false_eq_true])
  have dv_cache_0013 : y ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_y, not_false_eq_true])
  have dv_cache_0014 : x ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_D_x, not_false_eq_true])
  have dv_cache_0015 : y ∉ (D).fv :=
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
        simp only [dv_D_y, not_false_eq_true])
  have dv_cache_0016 : x ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_S_x, not_false_eq_true])
  have dv_cache_0017 : y ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_S_y, not_false_eq_true])
  have dv_cache_0018 : z ∉ (S).fv :=
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
        simp only [fresh_z_not_S, not_false_eq_true])
  have dv_cache_0019 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact (show x ≠ y from (by exact dv_x_y))
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_mpt2 x y z C D R
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0001 :=
    @g_eqtri F (syn_cmpt2 x C y D R)
      (syn_coprab x y z (syn_wa (syn_wa (.classMem (.cv x) C) (.classMem (.cv y) D))
          (.classEq (.cv z) R)))
      hyp_ovmpt2ga_2 p0000
  have p0002 :=
    @g_ov2ag x y z A B C D R S F H dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
      dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0001 dv_cache_0014
      dv_cache_0015 dv_cache_0002 dv_cache_0003 dv_cache_0016 dv_cache_0017 dv_cache_0018
      dv_cache_0019 dv_cache_0004 dv_cache_0005 hyp_ovmpt2ga_1 p0001
  exact p0002

@[expose]
noncomputable def g_ovmpt2g (x : Var) (y : Var) (A : Class) (B : Class) (C : Class)
    (D : Class) (R : Class) (S : Class) (F : Class) (G : Class) (H : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv)
    (dv_C_x : x ∉ C.fv) (dv_C_y : y ∉ C.fv) (dv_D_x : x ∉ D.fv) (dv_D_y : y ∉ D.fv)
    (_dv_G_x : x ∉ G.fv) (dv_S_x : x ∉ S.fv) (dv_S_y : y ∉ S.fv) (dv_x_y : x ≠ y)
    (hyp_ovmpt2g_1 : Nominal.NPrf (.imp (.classEq (.cv x) A) (.classEq R G)))
    (hyp_ovmpt2g_2 : Nominal.NPrf (.imp (.classEq (.cv y) B) (.classEq G S)))
    (hyp_ovmpt2g_3 : Nominal.NPrf (.classEq F (syn_cmpt2 x C y D R))) :
    Nominal.NPrf
      (.imp (syn_w3a (.classMem A C) (.classMem B D) (.classMem S H))
        (.classEq (syn_co A F B) S)) :=
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
  have dv_cache_0003 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_x, not_false_eq_true])
  have dv_cache_0004 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_y, not_false_eq_true])
  have dv_cache_0005 : x ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_x, not_false_eq_true])
  have dv_cache_0006 : y ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_y, not_false_eq_true])
  have dv_cache_0007 : x ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_D_x, not_false_eq_true])
  have dv_cache_0008 : y ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_D_y, not_false_eq_true])
  have dv_cache_0009 : x ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_S_x, not_false_eq_true])
  have dv_cache_0010 : y ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_S_y, not_false_eq_true])
  have dv_cache_0011 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show x ≠ y from (by exact dv_x_y))
  have p0000 :=
    @g_sylan9eq (.classEq (.cv x) A) (.classEq (.cv y) B) R G S hyp_ovmpt2g_1
      hyp_ovmpt2g_2
  have p0001 :=
    @g_ovmpt2ga x y A B C D R S F H dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
      dv_cache_0010 dv_cache_0011 p0000 hyp_ovmpt2g_3
  exact p0001


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk012BCompact001Part017`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_ovmpt2 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class)
    (D : Class) (R : Class) (S : Class) (F : Class) (G : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_C_x : x ∉ C.fv)
    (dv_C_y : y ∉ C.fv) (dv_D_x : x ∉ D.fv) (dv_D_y : y ∉ D.fv) (dv_G_x : x ∉ G.fv)
    (dv_S_x : x ∉ S.fv) (dv_S_y : y ∉ S.fv) (dv_x_y : x ≠ y)
    (hyp_ovmpt2g_1 : Nominal.NPrf (.imp (.classEq (.cv x) A) (.classEq R G)))
    (hyp_ovmpt2g_2 : Nominal.NPrf (.imp (.classEq (.cv y) B) (.classEq G S)))
    (hyp_ovmpt2g_3 : Nominal.NPrf (.classEq F (syn_cmpt2 x C y D R)))
    (hyp_ovmpt2_4 : Nominal.NPrf (.classMem S (syn_cvv))) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A C) (.classMem B D)) (.classEq (syn_co A F B) S)) :=
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
  have dv_cache_0003 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_x, not_false_eq_true])
  have dv_cache_0004 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_y, not_false_eq_true])
  have dv_cache_0005 : x ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_x, not_false_eq_true])
  have dv_cache_0006 : y ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_y, not_false_eq_true])
  have dv_cache_0007 : x ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_D_x, not_false_eq_true])
  have dv_cache_0008 : y ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_D_y, not_false_eq_true])
  have dv_cache_0009 : x ∉ (G).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_G_x, not_false_eq_true])
  have dv_cache_0010 : x ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_S_x, not_false_eq_true])
  have dv_cache_0011 : y ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_S_y, not_false_eq_true])
  have dv_cache_0012 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show x ≠ y from (by exact dv_x_y))
  have p0000 :=
    @g_ovmpt2g x y A B C D R S F G (syn_cvv) dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
      dv_cache_0010 dv_cache_0011 dv_cache_0012 hyp_ovmpt2g_1 hyp_ovmpt2g_2 hyp_ovmpt2g_3
  have p0001 :=
    @g_mp3an3 (.classMem A C) (.classMem B D) (.classMem S (syn_cvv))
      (.classEq (syn_co A F B) S) hyp_ovmpt2_4 p0000
  exact p0001

@[expose]
noncomputable def g_mptv (x : Var) (y : Var) (B : Class) (dv_B_y : y ∉ B.fv)
    (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.classEq (syn_cmpt x (syn_cvv) B) (syn_copab x y (.classEq (.cv y) B))) :=
  by
  have dv_cache_0001 : y ∉ ((syn_cvv)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
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
  have dv_cache_0003 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show x ≠ y from (by exact dv_x_y))
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_mpt x y (syn_cvv) B
      dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 := @g_vex x
  have p0002 := @g_biantrur (.classMem (.cv x) (syn_cvv)) (.classEq (.cv y) B) p0001
  have p0003 :=
    @g_opabbii (.classEq (.cv y) B)
      (syn_wa (.classMem (.cv x) (syn_cvv)) (.classEq (.cv y) B)) x y p0002
  have p0004 :=
    @g_eqtr4i (syn_cmpt x (syn_cvv) B)
      (syn_copab x y (syn_wa (.classMem (.cv x) (syn_cvv)) (.classEq (.cv y) B)))
      (syn_copab x y (.classEq (.cv y) B)) p0000 p0003
  exact p0004

@[expose]
noncomputable def g_f1od (ph : Wff) (x : Var) (y : Var) (A : Class) (B : Class)
    (C : Class) (D : Class) (F : Class) (W : Class) (X : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_C_y : y ∉ C.fv)
    (dv_D_x : x ∉ D.fv) (dv_ph_x : x ∉ ph.fv) (dv_ph_y : y ∉ ph.fv) (dv_x_y : x ≠ y)
    (hyp_f1od_1 : Nominal.NPrf (.classEq F (syn_cmpt x A C)))
    (hyp_f1od_2 : Nominal.NPrf (.imp (syn_wa ph (.classMem (.cv x) A)) (.classMem C W)))
    (hyp_f1od_3 : Nominal.NPrf (.imp (syn_wa ph (.classMem (.cv y) B)) (.classMem D X)))
    (hyp_f1od_4 : Nominal.NPrf (.imp ph
          (syn_wb (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) C))
            (syn_wa (.classMem (.cv y) B) (.classEq (.cv x) D))))) :
    Nominal.NPrf (.imp ph (syn_wf1o F A B)) :=
  by
  have dv_cache_0001 : x ∉ (ph).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_ph_x, not_false_eq_true])
  have dv_cache_0002 : x ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have dv_cache_0003 : y ∉ (ph).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_ph_y, not_false_eq_true])
  have dv_cache_0004 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_y, not_false_eq_true])
  have dv_cache_0005 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_y, not_false_eq_true])
  have dv_cache_0006 : y ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_y, not_false_eq_true])
  have dv_cache_0007 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0008 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_x, not_false_eq_true])
  have dv_cache_0009 : x ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_D_x, not_false_eq_true])
  have dv_cache_0010 : y ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show y ≠ x from (by exact Ne.symm dv_x_y))
  have p0000 := @g_ralrimiva ph (.classMem C W) x A dv_cache_0001 hyp_f1od_2
  have p0001 := @g_fnmpt x A C F W dv_cache_0002 hyp_f1od_1
  have p0002 := @g_syl ph (syn_wral x A (.classMem C W)) (syn_wfn F A) p0000 p0001
  have p0003 := @g_ralrimiva ph (.classMem D X) y B dv_cache_0003 hyp_f1od_3
  have p0004 := @g_eqid (syn_cmpt y B D)
  have p0005 := @g_fnmpt y B D (syn_cmpt y B D) X dv_cache_0004 p0004
  have p0006 :=
    @g_syl ph (syn_wral y B (.classMem D X)) (syn_wfn (syn_cmpt y B D) B) p0003 p0005
  have p0007 :=
    @g_opabbidv ph (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) C))
      (syn_wa (.classMem (.cv y) B) (.classEq (.cv x) D)) y x dv_cache_0003 dv_cache_0001
      hyp_f1od_4
  have p0008 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_mpt x y A C
      dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0009 :=
    @g_eqtri F (syn_cmpt x A C)
      (syn_copab x y (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) C))) hyp_f1od_1 p0008
  have p0010 :=
    @g_cnveqi F (syn_copab x y (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) C))) p0009
  have p0011 :=
    @g_cnvopab (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) C)) x y dv_cache_0007
  have p0012 :=
    @g_eqtri (syn_ccnv F)
      (syn_ccnv (syn_copab x y (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) C))))
      (syn_copab y x (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) C))) p0010 p0011
  have p0013 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_mpt y x B D
      dv_cache_0008 dv_cache_0009 dv_cache_0010
  have p0014 :=
    @g_n_3eqtr4g ph (syn_copab y x (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) C)))
      (syn_copab y x (syn_wa (.classMem (.cv y) B) (.classEq (.cv x) D))) (syn_ccnv F)
      (syn_cmpt y B D) p0007 p0012 p0013
  have p0015 := @g_fneq1d ph B (syn_ccnv F) (syn_cmpt y B D) p0014
  have p0016 :=
    @g_mpbird ph (syn_wfn (syn_ccnv F) B) (syn_wfn (syn_cmpt y B D) B) p0006 p0015
  have p0017 := @g_dff1o4 A B F
  have p0018 :=
    @g_sylanbrc ph (syn_wfn F A) (syn_wfn (syn_ccnv F) B) (syn_wf1o F A B) p0002 p0016
      p0017
  exact p0018

@[expose]
noncomputable def g_f1o2d (ph : Wff) (x : Var) (y : Var) (A : Class) (B : Class)
    (C : Class) (D : Class) (F : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv)
    (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_C_y : y ∉ C.fv) (dv_D_x : x ∉ D.fv)
    (dv_ph_x : x ∉ ph.fv) (dv_ph_y : y ∉ ph.fv) (dv_x_y : x ≠ y)
    (hyp_f1od_1 : Nominal.NPrf (.classEq F (syn_cmpt x A C)))
    (hyp_f1o2d_2 : Nominal.NPrf (.imp (syn_wa ph (.classMem (.cv x) A)) (.classMem C B)))
    (hyp_f1o2d_3 : Nominal.NPrf (.imp (syn_wa ph (.classMem (.cv y) B)) (.classMem D A)))
    (hyp_f1o2d_4 : Nominal.NPrf
        (.imp (syn_wa ph (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)))
          (syn_wb (.classEq (.cv x) D) (.classEq (.cv y) C)))) :
    Nominal.NPrf (.imp ph (syn_wf1o F A B)) :=
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
  have dv_cache_0003 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_x, not_false_eq_true])
  have dv_cache_0004 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_y, not_false_eq_true])
  have dv_cache_0005 : y ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_y, not_false_eq_true])
  have dv_cache_0006 : x ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_D_x, not_false_eq_true])
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
        simp only [dv_ph_x, not_false_eq_true])
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
        simp only [dv_ph_y, not_false_eq_true])
  have dv_cache_0009 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show x ≠ y from (by exact dv_x_y))
  have p0000 := @g_eleq1a C B (.cv y)
  have p0001 :=
    @g_syl (syn_wa ph (.classMem (.cv x) A)) (.classMem C B)
      (.imp (.classEq (.cv y) C) (.classMem (.cv y) B)) hyp_f1o2d_2 p0000
  have p0002 :=
    @g_impr ph (.classMem (.cv x) A) (.classEq (.cv y) C) (.classMem (.cv y) B) p0001
  have p0003 :=
    @g_biimpar (syn_wa ph (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)))
      (.classEq (.cv x) D) (.classEq (.cv y) C) hyp_f1o2d_4
  have p0004 :=
    @g_exp42 ph (.classMem (.cv x) A) (.classMem (.cv y) B) (.classEq (.cv y) C)
      (.classEq (.cv x) D) p0003
  have p0005 :=
    @g_com34 ph (.classMem (.cv x) A) (.classMem (.cv y) B) (.classEq (.cv y) C)
      (.classEq (.cv x) D) p0004
  have p0006 :=
    @g_imp32 ph (.classMem (.cv x) A) (.classEq (.cv y) C)
      (.imp (.classMem (.cv y) B) (.classEq (.cv x) D)) p0005
  have p0007 :=
    @g_jcai (syn_wa ph (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) C)))
      (.classMem (.cv y) B) (.classEq (.cv x) D) p0002 p0006
  have p0008 := @g_eleq1a D A (.cv x)
  have p0009 :=
    @g_syl (syn_wa ph (.classMem (.cv y) B)) (.classMem D A)
      (.imp (.classEq (.cv x) D) (.classMem (.cv x) A)) hyp_f1o2d_3 p0008
  have p0010 :=
    @g_impr ph (.classMem (.cv y) B) (.classEq (.cv x) D) (.classMem (.cv x) A) p0009
  have p0011 :=
    @g_biimpa (syn_wa ph (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)))
      (.classEq (.cv x) D) (.classEq (.cv y) C) hyp_f1o2d_4
  have p0012 :=
    @g_exp42 ph (.classMem (.cv x) A) (.classMem (.cv y) B) (.classEq (.cv x) D)
      (.classEq (.cv y) C) p0011
  have p0013 :=
    @g_com23 ph (.classMem (.cv x) A) (.classMem (.cv y) B)
      (.imp (.classEq (.cv x) D) (.classEq (.cv y) C)) p0012
  have p0014 :=
    @g_com34 ph (.classMem (.cv y) B) (.classMem (.cv x) A) (.classEq (.cv x) D)
      (.classEq (.cv y) C) p0013
  have p0015 :=
    @g_imp32 ph (.classMem (.cv y) B) (.classEq (.cv x) D)
      (.imp (.classMem (.cv x) A) (.classEq (.cv y) C)) p0014
  have p0016 :=
    @g_jcai (syn_wa ph (syn_wa (.classMem (.cv y) B) (.classEq (.cv x) D)))
      (.classMem (.cv x) A) (.classEq (.cv y) C) p0010 p0015
  have p0017 :=
    @g_impbida ph (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) C))
      (syn_wa (.classMem (.cv y) B) (.classEq (.cv x) D)) p0007 p0016
  have p0018 :=
    @g_f1od ph x y A B C D F B A dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 hyp_f1od_1
      hyp_f1o2d_2 hyp_f1o2d_3 p0017
  exact p0018


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk012BCompact001Part018`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_fmpt2x (x : Var) (y : Var) (A : Class) (B : Class) (C : Class)
    (D : Class) (F : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_y : y ∉ B.fv)
    (dv_D_x : x ∉ D.fv) (dv_D_y : y ∉ D.fv) (dv_x_y : x ≠ y)
    (hyp_fmpt2x_1 : Nominal.NPrf (.classEq F (syn_cmpt2 x A y B C))) :
    Nominal.NPrf
      (syn_wb (syn_wral x A (syn_wral y B (.classMem C D)))
        (syn_wf F (syn_ciun x A (syn_cxp (syn_csn (.cv x)) B)) D)) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv ∪ D.fv ∪ F.fv
  let z : Var := freshVar proofSupport 0
  let w : Var := freshVar proofSupport 1
  let v : Var := freshVar proofSupport 2
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))
  have fresh_y_ne_z : y ≠ z := Ne.symm fresh_z_ne_y
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_z_not_C : z ∉ C.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_not_D : z ∉ D.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))))
  have fresh_x_ne_w : x ≠ w := Ne.symm fresh_w_ne_x
  have fresh_w_ne_y : w ≠ y := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))
  have fresh_y_ne_w : y ≠ w := Ne.symm fresh_w_ne_y
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_w_not_B : w ∉ B.fv := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_w_not_C : w ∉ C.fv := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_w_not_D : w ∉ D.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_v : v ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_v_ne_x : v ≠ x := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))))
  have fresh_x_ne_v : x ≠ v := Ne.symm fresh_v_ne_x
  have fresh_v_ne_y : v ≠ y := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))
  have fresh_y_ne_v : y ≠ v := Ne.symm fresh_v_ne_y
  have fresh_v_not_A : v ∉ A.fv := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_v_not_B : v ∉ B.fv := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_v_not_C : v ∉ C.fv := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_v_not_D : v ∉ D.fv := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_ne_w : z ≠ w :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_w_ne_z : w ≠ z := Ne.symm fresh_z_ne_w
  have fresh_z_ne_v : z ≠ v :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_v_ne_z : v ≠ z := Ne.symm fresh_z_ne_v
  have fresh_w_ne_v : w ≠ v :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_v_ne_w : v ≠ w := Ne.symm fresh_w_ne_v
  have dv_cache_0001 : x ∉ ((Wff.classEq (.cv v) (syn_cop (.cv z) (.cv w)))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_v, fresh_x_ne_z, fresh_x_ne_w, or_false,
          not_false_eq_true])
  have dv_cache_0002 : v ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_v_not_A, not_false_eq_true])
  have dv_cache_0003 : z ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_A, not_false_eq_true])
  have dv_cache_0004 : w ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_A, not_false_eq_true])
  have dv_cache_0005 : v ∉ ((syn_csb (.cv z) x B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csb,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_v_ne_z, fresh_v_not_B, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0006 : w ∉ ((syn_csb (.cv z) x B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csb,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_w_ne_z, fresh_w_not_B, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0007 :
    z ∉
      ((Wff.classMem (syn_csb (syn_cfv (syn_c1st) (.cv v)) x
            (syn_csb (syn_cfv (syn_c2nd) (.cv v)) y C)) D)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csb,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_z_ne_v, fresh_z_not_C,
          fresh_z_not_D, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0008 :
    w ∉
      ((Wff.classMem (syn_csb (syn_cfv (syn_c1st) (.cv v)) x
            (syn_csb (syn_cfv (syn_c2nd) (.cv v)) y C)) D)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csb,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_w_ne_v, fresh_w_not_C,
          fresh_w_not_D, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0009 :
    v ∉ ((Wff.classMem (syn_csb (.cv z) x (syn_csb (.cv w) y C)) D)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csb,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_v_ne_z, fresh_v_ne_w, fresh_v_not_C, fresh_v_not_D,
          or_false, and_false, not_false_eq_true])
  have dv_cache_0010 : v ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show v ≠ z from (by exact fresh_v_ne_z))
  have dv_cache_0011 : v ≠ w :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show v ≠ w from (by exact fresh_v_ne_w))
  have dv_cache_0012 : z ≠ w :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show z ≠ w from (by exact fresh_z_ne_w))
  have dv_cache_0013 :
    z ∉
      ((syn_wa (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)) (.classEq (.cv v) C))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_x, fresh_z_not_A, fresh_z_ne_y, fresh_z_not_B,
          fresh_z_ne_v, fresh_z_not_C, or_false, not_false_eq_true])
  have dv_cache_0014 :
    w ∉
      ((syn_wa (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)) (.classEq (.cv v) C))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_x, fresh_w_not_A, fresh_w_ne_y, fresh_w_not_B,
          fresh_w_ne_v, fresh_w_not_C, or_false, not_false_eq_true])
  have dv_cache_0015 : x ∉ ((Wff.classMem (.cv z) A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_z, dv_A_x, or_false, not_false_eq_true])
  have dv_cache_0016 : x ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_z, not_false_eq_true])
  have dv_cache_0017 : x ≠ w :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (show x ≠ w from (by exact fresh_x_ne_w))
  have dv_cache_0018 : x ∉ ((Class.cv v)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_v, not_false_eq_true])
  have dv_cache_0019 :
    y ∉ ((syn_wa (.classMem (.cv z) A) (.classMem (.cv w) (syn_csb (.cv z) x B)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csb, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_y_ne_z, dv_A_y, fresh_y_ne_w,
          dv_B_y, or_false, and_false, not_false_eq_true])
  have dv_cache_0020 : y ∉ ((Class.cv z)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_z, not_false_eq_true])
  have dv_cache_0021 : y ∉ ((Class.cv w)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_w, not_false_eq_true])
  have dv_cache_0022 : y ∉ ((Class.cv v)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_v, not_false_eq_true])
  have dv_cache_0023 : w ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (show w ≠ z from (by exact fresh_w_ne_z))
  have dv_cache_0024 : w ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (show w ≠ x from (by exact fresh_w_ne_x))
  have dv_cache_0025 : w ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024
    exact (show w ≠ y from (by exact fresh_w_ne_y))
  have dv_cache_0026 : w ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025
    exact (show w ≠ v from (by exact fresh_w_ne_v))
  have dv_cache_0027 : z ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact (show z ≠ x from (by exact fresh_z_ne_x))
  have dv_cache_0028 : z ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact (show z ≠ y from (by exact fresh_z_ne_y))
  have dv_cache_0029 : z ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact (show z ≠ v from (by exact fresh_z_ne_v))
  have dv_cache_0030 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0031 : x ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030
    exact (show x ≠ v from (by exact fresh_x_ne_v))
  have dv_cache_0032 : y ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031
    exact (show y ≠ v from (by exact fresh_y_ne_v))
  have dv_cache_0033 : v ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_v_not_B, not_false_eq_true])
  have dv_cache_0034 : v ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_v_not_C, not_false_eq_true])
  have dv_cache_0035 : v ∉ ((syn_csb (.cv z) x (syn_csb (.cv w) y C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csb,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_v_ne_z, fresh_v_ne_w, fresh_v_not_C, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0036 :
    z ∉
      ((syn_csb (syn_cfv (syn_c1st) (.cv v)) x
          (syn_csb (syn_cfv (syn_c2nd) (.cv v)) y C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csb,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_z_ne_v, fresh_z_not_C,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0037 :
    w ∉
      ((syn_csb (syn_cfv (syn_c1st) (.cv v)) x
          (syn_csb (syn_cfv (syn_c2nd) (.cv v)) y C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csb,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_w_ne_v, fresh_w_not_C,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0038 :
    v ∉ ((syn_ciun z A (syn_cxp (syn_csn (.cv z)) (syn_csb (.cv z) x B)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ciun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csb, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_v_not_A, fresh_v_ne_z,
          fresh_v_not_B, or_false, and_false, not_false_eq_true])
  have dv_cache_0039 : v ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_v_not_D, not_false_eq_true])
  have dv_cache_0040 : z ∉ ((syn_wral y B (.classMem C D))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union,
          Finset.mem_erase, fresh_z_not_B, fresh_z_not_C, fresh_z_not_D, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0041 : x ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_D_x, not_false_eq_true])
  have dv_cache_0042 : w ∉ ((Wff.classMem C D)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union,
          fresh_w_not_C, fresh_w_not_D, or_false, not_false_eq_true])
  have dv_cache_0043 : y ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_D_y, not_false_eq_true])
  have dv_cache_0044 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_y, not_false_eq_true])
  have dv_cache_0045 : w ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_B, not_false_eq_true])
  have dv_cache_0046 : w ∉ ((Wff.classEq (.cv x) (.cv z))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_x, fresh_w_ne_z, or_false, not_false_eq_true])
  have dv_cache_0047 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have dv_cache_0048 : z ∉ ((syn_cxp (syn_csn (.cv x)) B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_x, fresh_z_not_B, or_false, not_false_eq_true])
  have dv_cache_0049 : x ∉ ((syn_csn (.cv z))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_x_ne_z,
          not_false_eq_true])
  have p0000 := @g_vex z
  have p0001 := @g_vex w
  have p0002 := @g_op1std (.cv z) (.cv w) (.cv v) p0000 p0001
  have p0003 :=
    @g_csbeq1d (.classEq (.cv v) (syn_cop (.cv z) (.cv w))) x (syn_cfv (syn_c1st) (.cv v))
      (.cv z) (syn_csb (syn_cfv (syn_c2nd) (.cv v)) y C) p0002
  have p0004 := @g_op2ndd (.cv z) (.cv w) (.cv v) p0000 p0001
  have p0005 :=
    @g_csbeq1d (.classEq (.cv v) (syn_cop (.cv z) (.cv w))) y (syn_cfv (syn_c2nd) (.cv v))
      (.cv w) C p0004
  have p0006 :=
    @g_csbeq2dv (.classEq (.cv v) (syn_cop (.cv z) (.cv w))) x (.cv z)
      (syn_csb (syn_cfv (syn_c2nd) (.cv v)) y C) (syn_csb (.cv w) y C) dv_cache_0001 p0005
  have p0007 :=
    @g_eqtrd (.classEq (.cv v) (syn_cop (.cv z) (.cv w)))
      (syn_csb (syn_cfv (syn_c1st) (.cv v)) x (syn_csb (syn_cfv (syn_c2nd) (.cv v)) y C))
      (syn_csb (.cv z) x (syn_csb (syn_cfv (syn_c2nd) (.cv v)) y C))
      (syn_csb (.cv z) x (syn_csb (.cv w) y C)) p0003 p0006
  have p0008 :=
    @g_eleq1d (.classEq (.cv v) (syn_cop (.cv z) (.cv w)))
      (syn_csb (syn_cfv (syn_c1st) (.cv v)) x (syn_csb (syn_cfv (syn_c2nd) (.cv v)) y C))
      (syn_csb (.cv z) x (syn_csb (.cv w) y C)) D p0007
  have p0009 :=
    @g_raliunxp
      (.classMem (syn_csb (syn_cfv (syn_c1st) (.cv v)) x
          (syn_csb (syn_cfv (syn_c2nd) (.cv v)) y C)) D)
      (.classMem (syn_csb (.cv z) x (syn_csb (.cv w) y C)) D) v z w A
      (syn_csb (.cv z) x B) dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 p0008
  have p0010 :=
    @g_nfv
      (syn_wa (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)) (.classEq (.cv v) C)) z
      dv_cache_0013
  have p0011 :=
    @g_nfv
      (syn_wa (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)) (.classEq (.cv v) C)) w
      dv_cache_0014
  have p0012 := @g_nfv (.classMem (.cv z) A) x dv_cache_0015
  have p0013 := @g_nfcsb1v x (.cv z) B dv_cache_0016
  have p0014 := @g_nfcri x w (syn_csb (.cv z) x B) dv_cache_0017 p0013
  have p0015 :=
    @g_nfan (.classMem (.cv z) A) (.classMem (.cv w) (syn_csb (.cv z) x B)) x p0012 p0014
  have p0016 := @g_nfcsb1v x (.cv z) (syn_csb (.cv w) y C) dv_cache_0016
  have p0017 :=
    @g_nfeq2 x (.cv v) (syn_csb (.cv z) x (syn_csb (.cv w) y C)) dv_cache_0018 p0016
  have p0018 :=
    @g_nfan (syn_wa (.classMem (.cv z) A) (.classMem (.cv w) (syn_csb (.cv z) x B)))
      (.classEq (.cv v) (syn_csb (.cv z) x (syn_csb (.cv w) y C))) x p0015 p0017
  have p0019 :=
    @g_nfv (syn_wa (.classMem (.cv z) A) (.classMem (.cv w) (syn_csb (.cv z) x B))) y
      dv_cache_0019
  have p0020 := @g_nfcv y (.cv z) dv_cache_0020
  have p0021 := @g_nfcsb1v y (.cv w) C dv_cache_0021
  have p0022 := @g_nfcsb y x (.cv z) (syn_csb (.cv w) y C) p0020 p0021
  have p0023 :=
    @g_nfeq2 y (.cv v) (syn_csb (.cv z) x (syn_csb (.cv w) y C)) dv_cache_0022 p0022
  have p0024 :=
    @g_nfan (syn_wa (.classMem (.cv z) A) (.classMem (.cv w) (syn_csb (.cv z) x B)))
      (.classEq (.cv v) (syn_csb (.cv z) x (syn_csb (.cv w) y C))) y p0019 p0023
  have p0025 := @g_eleq1 (.cv x) (.cv z) A
  have p0026 :=
    @g_adantr (.classEq (.cv x) (.cv z))
      (syn_wb (.classMem (.cv x) A) (.classMem (.cv z) A)) (.classEq (.cv y) (.cv w))
      p0025
  have p0027 := @g_eleq1 (.cv y) (.cv w) B
  have p0028 := @g_csbeq1a x (.cv z) B
  have p0029 := @g_eleq2d (.classEq (.cv x) (.cv z)) B (syn_csb (.cv z) x B) (.cv w) p0028
  have p0030 :=
    @g_sylan9bbr (.classEq (.cv y) (.cv w)) (.classMem (.cv y) B) (.classMem (.cv w) B)
      (.classEq (.cv x) (.cv z)) (.classMem (.cv w) (syn_csb (.cv z) x B)) p0027 p0029
  have p0031 :=
    @g_anbi12d (syn_wa (.classEq (.cv x) (.cv z)) (.classEq (.cv y) (.cv w)))
      (.classMem (.cv x) A) (.classMem (.cv z) A) (.classMem (.cv y) B)
      (.classMem (.cv w) (syn_csb (.cv z) x B)) p0026 p0030
  have p0032 := @g_csbeq1a y (.cv w) C
  have p0033 := @g_csbeq1a x (.cv z) (syn_csb (.cv w) y C)
  have p0034 :=
    @g_sylan9eqr (.classEq (.cv y) (.cv w)) (.classEq (.cv x) (.cv z)) C
      (syn_csb (.cv w) y C) (syn_csb (.cv z) x (syn_csb (.cv w) y C)) p0032 p0033
  have p0035 :=
    @g_eqeq2d (syn_wa (.classEq (.cv x) (.cv z)) (.classEq (.cv y) (.cv w))) C
      (syn_csb (.cv z) x (syn_csb (.cv w) y C)) (.cv v) p0034
  have p0036 :=
    @g_anbi12d (syn_wa (.classEq (.cv x) (.cv z)) (.classEq (.cv y) (.cv w)))
      (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B))
      (syn_wa (.classMem (.cv z) A) (.classMem (.cv w) (syn_csb (.cv z) x B)))
      (.classEq (.cv v) C) (.classEq (.cv v) (syn_csb (.cv z) x (syn_csb (.cv w) y C)))
      p0031 p0035
  have p0037_e04_recanon :
    Nominal.NPrf
      (.imp (syn_wa (.objEq x z) (.objEq y w)) (syn_wb
          (syn_wa (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)) (.classEq (.cv v) C))
          (syn_wa (syn_wa (.classMem (.cv z) A) (.classMem (.cv w) (syn_csb (.cv z) x B)))
            (.classEq (.cv v) (syn_csb (.cv z) x (syn_csb (.cv w) y C)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_wb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0036
  have p0037 :=
    @g_cbvoprab12
      (syn_wa (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B)) (.classEq (.cv v) C))
      (syn_wa (syn_wa (.classMem (.cv z) A) (.classMem (.cv w) (syn_csb (.cv z) x B)))
        (.classEq (.cv v) (syn_csb (.cv z) x (syn_csb (.cv w) y C))))
      x y v z w dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
      dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 p0010 p0011
      p0018 p0024 p0037_e04_recanon
  have p0038 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_mpt2 x y v A B C
      dv_cache_0002 dv_cache_0033 dv_cache_0034 dv_cache_0031 dv_cache_0032
  have p0039 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_mpt2 z w v A
      (syn_csb (.cv z) x B) (syn_csb (.cv z) x (syn_csb (.cv w) y C)) dv_cache_0002
      dv_cache_0005 dv_cache_0035 dv_cache_0029 dv_cache_0026
  have p0040 :=
    @g_n_3eqtr4i
      (syn_coprab x y v (syn_wa (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B))
          (.classEq (.cv v) C)))
      (syn_coprab z w v
        (syn_wa (syn_wa (.classMem (.cv z) A) (.classMem (.cv w) (syn_csb (.cv z) x B)))
          (.classEq (.cv v) (syn_csb (.cv z) x (syn_csb (.cv w) y C)))))
      (syn_cmpt2 x A y B C)
      (syn_cmpt2 z A w (syn_csb (.cv z) x B) (syn_csb (.cv z) x (syn_csb (.cv w) y C)))
      p0037 p0038 p0039
  have p0041 :=
    @g_mpt2mptx z w v A (syn_csb (.cv z) x B)
      (syn_csb (syn_cfv (syn_c1st) (.cv v)) x (syn_csb (syn_cfv (syn_c2nd) (.cv v)) y C))
      (syn_csb (.cv z) x (syn_csb (.cv w) y C)) dv_cache_0003 dv_cache_0004 dv_cache_0002
      dv_cache_0006 dv_cache_0005 dv_cache_0036 dv_cache_0037 dv_cache_0035 dv_cache_0012
      dv_cache_0029 dv_cache_0026 p0007
  have p0042 :=
    @g_n_3eqtr4i (syn_cmpt2 x A y B C)
      (syn_cmpt2 z A w (syn_csb (.cv z) x B) (syn_csb (.cv z) x (syn_csb (.cv w) y C))) F
      (syn_cmpt v (syn_ciun z A (syn_cxp (syn_csn (.cv z)) (syn_csb (.cv z) x B)))
        (syn_csb (syn_cfv (syn_c1st) (.cv v)) x (syn_csb (syn_cfv (syn_c2nd) (.cv v)) y C)))
      p0040 hyp_fmpt2x_1 p0041
  have p0043 :=
    @g_fmpt v (syn_ciun z A (syn_cxp (syn_csn (.cv z)) (syn_csb (.cv z) x B))) D
      (syn_csb (syn_cfv (syn_c1st) (.cv v)) x (syn_csb (syn_cfv (syn_c2nd) (.cv v)) y C))
      F dv_cache_0038 dv_cache_0039 p0042
  have p0044 :=
    @g_bitr3i
      (syn_wral z A (syn_wral w (syn_csb (.cv z) x B)
          (.classMem (syn_csb (.cv z) x (syn_csb (.cv w) y C)) D)))
      (syn_wral v (syn_ciun z A (syn_cxp (syn_csn (.cv z)) (syn_csb (.cv z) x B))) (.classMem
          (syn_csb (syn_cfv (syn_c1st) (.cv v)) x (syn_csb (syn_cfv (syn_c2nd) (.cv v)) y C))
          D))
      (syn_wf F (syn_ciun z A (syn_cxp (syn_csn (.cv z)) (syn_csb (.cv z) x B))) D) p0009
      p0043
  have p0045 := @g_nfv (syn_wral y B (.classMem C D)) z dv_cache_0040
  have p0046 := @g_nfel1 x (syn_csb (.cv z) x (syn_csb (.cv w) y C)) D dv_cache_0041 p0016
  have p0047 :=
    @g_nfral (.classMem (syn_csb (.cv z) x (syn_csb (.cv w) y C)) D) x w
      (syn_csb (.cv z) x B) p0013 p0046
  have p0048 := @g_nfv (.classMem C D) w dv_cache_0042
  have p0049 := @g_nfel1 y (syn_csb (.cv w) y C) D dv_cache_0043 p0021
  have p0050 := @g_eleq1d (.classEq (.cv y) (.cv w)) C (syn_csb (.cv w) y C) D p0032
  have p0051_e02_recanon :
    Nominal.NPrf
      (.imp (.objEq y w) (syn_wb (.classMem C D) (.classMem (syn_csb (.cv w) y C) D))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_csb syn_wsbc
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0050
  have p0051 :=
    @g_cbvral (.classMem C D) (.classMem (syn_csb (.cv w) y C) D) y w B dv_cache_0044
      dv_cache_0045 p0048 p0049 p0051_e02_recanon
  have p0052 :=
    @g_eleq1d (.classEq (.cv x) (.cv z)) (syn_csb (.cv w) y C)
      (syn_csb (.cv z) x (syn_csb (.cv w) y C)) D p0033
  have p0053 :=
    @g_raleqbidv (.classEq (.cv x) (.cv z)) (.classMem (syn_csb (.cv w) y C) D)
      (.classMem (syn_csb (.cv z) x (syn_csb (.cv w) y C)) D) w B (syn_csb (.cv z) x B)
      dv_cache_0045 dv_cache_0006 dv_cache_0046 p0028 p0052
  have p0054 :=
    @g_syl5bb (syn_wral y B (.classMem C D))
      (syn_wral w B (.classMem (syn_csb (.cv w) y C) D)) (.classEq (.cv x) (.cv z))
      (syn_wral w (syn_csb (.cv z) x B) (.classMem (syn_csb (.cv z) x (syn_csb (.cv w) y C)) D))
      p0051 p0053
  have p0055_e02_recanon :
    Nominal.NPrf
      (.imp (.objEq x z) (syn_wb (syn_wral y B (.classMem C D))
          (syn_wral w (syn_csb (.cv z) x B)
            (.classMem (syn_csb (.cv z) x (syn_csb (.cv w) y C)) D)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wral
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0054
  have p0055 :=
    @g_cbvral (syn_wral y B (.classMem C D))
      (syn_wral w (syn_csb (.cv z) x B) (.classMem (syn_csb (.cv z) x (syn_csb (.cv w) y C)) D))
      x z A dv_cache_0047 dv_cache_0003 p0045 p0047 p0055_e02_recanon
  have p0056 := @g_nfcv z (syn_cxp (syn_csn (.cv x)) B) dv_cache_0048
  have p0057 := @g_nfcv x (syn_csn (.cv z)) dv_cache_0049
  have p0058 := @g_nfxp x (syn_csn (.cv z)) (syn_csb (.cv z) x B) p0057 p0013
  have p0059 := @g_sneq (.cv x) (.cv z)
  have p0060 :=
    @g_xpeq12d (.classEq (.cv x) (.cv z)) (syn_csn (.cv x)) (syn_csn (.cv z)) B
      (syn_csb (.cv z) x B) p0059 p0028
  have p0061_e02_recanon :
    Nominal.NPrf
      (.imp (.objEq x z) (.classEq (syn_cxp (syn_csn (.cv x)) B)
          (syn_cxp (syn_csn (.cv z)) (syn_csb (.cv z) x B)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cxp syn_copab syn_wex syn_wa syn_csn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csb]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0060
  have p0061 :=
    @g_cbviun x z A (syn_cxp (syn_csn (.cv x)) B)
      (syn_cxp (syn_csn (.cv z)) (syn_csb (.cv z) x B)) dv_cache_0047 dv_cache_0003 p0056
      p0058 p0061_e02_recanon
  have p0062 :=
    @g_feq2i (syn_ciun x A (syn_cxp (syn_csn (.cv x)) B))
      (syn_ciun z A (syn_cxp (syn_csn (.cv z)) (syn_csb (.cv z) x B))) D F p0061
  have p0063 :=
    @g_n_3bitr4i
      (syn_wral z A (syn_wral w (syn_csb (.cv z) x B)
          (.classMem (syn_csb (.cv z) x (syn_csb (.cv w) y C)) D)))
      (syn_wf F (syn_ciun z A (syn_cxp (syn_csn (.cv z)) (syn_csb (.cv z) x B))) D)
      (syn_wral x A (syn_wral y B (.classMem C D)))
      (syn_wf F (syn_ciun x A (syn_cxp (syn_csn (.cv x)) B)) D) p0044 p0055 p0062
  exact p0063

@[expose]
noncomputable def g_fmpt2 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class)
    (D : Class) (F : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv)
    (dv_B_y : y ∉ B.fv) (dv_D_x : x ∉ D.fv) (dv_D_y : y ∉ D.fv) (dv_x_y : x ≠ y)
    (hyp_fmpt2_1 : Nominal.NPrf (.classEq F (syn_cmpt2 x A y B C))) :
    Nominal.NPrf
      (syn_wb (syn_wral x A (syn_wral y B (.classMem C D))) (syn_wf F (syn_cxp A B) D)) :=
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
  have dv_cache_0003 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_y, not_false_eq_true])
  have dv_cache_0004 : x ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_D_x, not_false_eq_true])
  have dv_cache_0005 : y ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_D_y, not_false_eq_true])
  have dv_cache_0006 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show x ≠ y from (by exact dv_x_y))
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
        simp only [dv_B_x, not_false_eq_true])
  have p0000 :=
    @g_fmpt2x x y A B C D F dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 hyp_fmpt2_1
  have p0001 := @g_iunxpconst x A B dv_cache_0001 dv_cache_0007
  have p0002 :=
    @g_feq2i (syn_ciun x A (syn_cxp (syn_csn (.cv x)) B)) (syn_cxp A B) D F p0001
  have p0003 :=
    @g_bitri (syn_wral x A (syn_wral y B (.classMem C D)))
      (syn_wf F (syn_ciun x A (syn_cxp (syn_csn (.cv x)) B)) D) (syn_wf F (syn_cxp A B) D)
      p0000 p0002
  exact p0003


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk012BCompact001Part019`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_fnmpt2 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class)
    (F : Class) (V : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv)
    (dv_B_y : y ∉ B.fv) (dv_x_y : x ≠ y)
    (hyp_fmpt2_1 : Nominal.NPrf (.classEq F (syn_cmpt2 x A y B C))) :
    Nominal.NPrf
      (.imp (syn_wral x A (syn_wral y B (.classMem C V))) (syn_wfn F (syn_cxp A B))) :=
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
  have dv_cache_0003 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_x, not_false_eq_true])
  have dv_cache_0004 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_y, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((syn_cvv)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0006 : y ∉ ((syn_cvv)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0007 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show x ≠ y from (by exact dv_x_y))
  have p0000 := @g_elex C V
  have p0001 := @g_ralimi (.classMem C V) (.classMem C (syn_cvv)) y B p0000
  have p0002 :=
    @g_ralimi (syn_wral y B (.classMem C V)) (syn_wral y B (.classMem C (syn_cvv))) x A
      p0001
  have p0003 :=
    @g_fmpt2 x y A B C (syn_cvv) F dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007 hyp_fmpt2_1
  have p0004 := @g_dffn2 (syn_cxp A B) F
  have p0005 :=
    @g_bitr4i (syn_wral x A (syn_wral y B (.classMem C (syn_cvv))))
      (syn_wf F (syn_cxp A B) (syn_cvv)) (syn_wfn F (syn_cxp A B)) p0003 p0004
  have p0006 :=
    @g_sylib (syn_wral x A (syn_wral y B (.classMem C V)))
      (syn_wral x A (syn_wral y B (.classMem C (syn_cvv)))) (syn_wfn F (syn_cxp A B))
      p0002 p0005
  exact p0006

@[expose]
noncomputable def g_fnmpt2i (x : Var) (y : Var) (A : Class) (B : Class) (C : Class)
    (F : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv)
    (dv_B_y : y ∉ B.fv) (dv_x_y : x ≠ y)
    (hyp_fmpt2_1 : Nominal.NPrf (.classEq F (syn_cmpt2 x A y B C)))
    (hyp_fnmpt2i_2 : Nominal.NPrf (.classMem C (syn_cvv))) :
    Nominal.NPrf (syn_wfn F (syn_cxp A B)) :=
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
  have dv_cache_0003 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_x, not_false_eq_true])
  have dv_cache_0004 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_y, not_false_eq_true])
  have dv_cache_0005 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ y from (by exact dv_x_y))
  have p0000 := @g_rgen2w (.classMem C (syn_cvv)) x y A B hyp_fnmpt2i_2
  have p0001 :=
    @g_fnmpt2 x y A B C F (syn_cvv) dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 hyp_fmpt2_1
  have p0002 := Nominal.mp p0000 p0001
  exact p0002

@[expose]
noncomputable def g_brsnsi (A : Class) (B : Class) (R : Class)
    (hyp_brsnsi_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_brsnsi_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (syn_wb (syn_wbr (syn_csn A) (syn_csi R) (syn_csn B)) (syn_wbr A R B)) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ R.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  let w : Var := freshVar proofSupport 3
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
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
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
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
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_R : z ∉ R.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_w_not_B : w ∉ B.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_w_not_R : w ∉ R.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
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
  have fresh_x_ne_w : x ≠ w :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_w_ne_x : w ≠ x := Ne.symm fresh_x_ne_w
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y := Ne.symm fresh_y_ne_z
  have fresh_y_ne_w : y ≠ w :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_w_ne_y : w ≠ y := Ne.symm fresh_y_ne_w
  have fresh_z_ne_w : z ≠ w :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have dv_cache_0001 : x ∉ ((Wff.classEq (.cv z) (syn_csn A))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_z, fresh_x_not_A, or_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((Wff.classEq (.cv z) (syn_csn A))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_z, fresh_y_not_A, or_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((Wff.classEq (.cv w) (syn_csn B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_w, fresh_x_not_B, or_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ ((Wff.classEq (.cv w) (syn_csn B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_w, fresh_y_not_B, or_false, not_false_eq_true])
  have dv_cache_0005 : y ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_R, not_false_eq_true])
  have dv_cache_0006 : z ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_R, not_false_eq_true])
  have dv_cache_0007 : w ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_R, not_false_eq_true])
  have dv_cache_0008 : x ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_R, not_false_eq_true])
  have dv_cache_0009 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0010 : y ≠ w :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show y ≠ w from (by exact fresh_y_ne_w))
  have dv_cache_0011 : y ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show y ≠ x from (by exact fresh_y_ne_x))
  have dv_cache_0012 : z ≠ w :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show z ≠ w from (by exact fresh_z_ne_w))
  have dv_cache_0013 : z ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact (show z ≠ x from (by exact fresh_z_ne_x))
  have dv_cache_0014 : w ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact (show w ≠ x from (by exact fresh_w_ne_x))
  have dv_cache_0015 : z ∉ ((syn_csn A)).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, fresh_z_not_A,
          not_false_eq_true])
  have dv_cache_0016 : w ∉ ((syn_csn A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, fresh_w_not_A,
          not_false_eq_true])
  have dv_cache_0017 : z ∉ ((syn_csn B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, fresh_z_not_B,
          not_false_eq_true])
  have dv_cache_0018 : w ∉ ((syn_csn B)).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, fresh_w_not_B,
          not_false_eq_true])
  have dv_cache_0019 :
    z ∉
      ((syn_wex x (syn_wex y (syn_w3a (.classEq (.cv x) A) (.classEq (.cv y) B)
              (syn_wbr (.cv x) R (.cv y)))))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_y,
          fresh_z_not_R, fresh_z_not_A, fresh_z_not_B, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0020 :
    w ∉
      ((syn_wex x (syn_wex y (syn_w3a (.classEq (.cv x) A) (.classEq (.cv y) B)
              (syn_wbr (.cv x) R (.cv y)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_w_ne_x, fresh_w_ne_y,
          fresh_w_not_R, fresh_w_not_A, fresh_w_not_B, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0021 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0022 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0023 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_B, not_false_eq_true])
  have dv_cache_0024 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_B, not_false_eq_true])
  have dv_cache_0025 : y ∉ ((syn_wbr A R B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          fresh_y_not_A, fresh_y_not_B, fresh_y_not_R, or_false, not_false_eq_true])
  have dv_cache_0026 : x ∉ ((syn_wbr A R (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_not_A, fresh_x_ne_y, fresh_x_not_R, or_false,
          not_false_eq_true])
  have dv_cache_0027 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 := @g_snex A
  have p0001 := @g_snex B
  have p0002 := @g_eqeq1 (.cv z) (syn_csn A) (syn_csn (.cv x))
  have p0003 := @g_eqcom (syn_csn A) (syn_csn (.cv x))
  have p0004 := @g_vex x
  have p0005 := @g_sneqb (.cv x) A p0004
  have p0006 :=
    @g_bitri (.classEq (syn_csn A) (syn_csn (.cv x)))
      (.classEq (syn_csn (.cv x)) (syn_csn A)) (.classEq (.cv x) A) p0003 p0005
  have p0007 :=
    @g_syl6bb (.classEq (.cv z) (syn_csn A)) (.classEq (.cv z) (syn_csn (.cv x)))
      (.classEq (syn_csn A) (syn_csn (.cv x))) (.classEq (.cv x) A) p0002 p0006
  have p0008 :=
    @g_n_3anbi1d (.classEq (.cv z) (syn_csn A)) (.classEq (.cv z) (syn_csn (.cv x)))
      (.classEq (.cv x) A) (.classEq (.cv w) (syn_csn (.cv y)))
      (syn_wbr (.cv x) R (.cv y)) p0007
  have p0009 :=
    @g_n_2exbidv (.classEq (.cv z) (syn_csn A))
      (syn_w3a (.classEq (.cv z) (syn_csn (.cv x))) (.classEq (.cv w) (syn_csn (.cv y)))
        (syn_wbr (.cv x) R (.cv y)))
      (syn_w3a (.classEq (.cv x) A) (.classEq (.cv w) (syn_csn (.cv y)))
        (syn_wbr (.cv x) R (.cv y)))
      x y dv_cache_0001 dv_cache_0002 p0008
  have p0010 := @g_eqeq1 (.cv w) (syn_csn B) (syn_csn (.cv y))
  have p0011 := @g_eqcom (syn_csn B) (syn_csn (.cv y))
  have p0012 := @g_vex y
  have p0013 := @g_sneqb (.cv y) B p0012
  have p0014 :=
    @g_bitri (.classEq (syn_csn B) (syn_csn (.cv y)))
      (.classEq (syn_csn (.cv y)) (syn_csn B)) (.classEq (.cv y) B) p0011 p0013
  have p0015 :=
    @g_syl6bb (.classEq (.cv w) (syn_csn B)) (.classEq (.cv w) (syn_csn (.cv y)))
      (.classEq (syn_csn B) (syn_csn (.cv y))) (.classEq (.cv y) B) p0010 p0014
  have p0016 :=
    @g_n_3anbi2d (.classEq (.cv w) (syn_csn B)) (.classEq (.cv w) (syn_csn (.cv y)))
      (.classEq (.cv y) B) (.classEq (.cv x) A) (syn_wbr (.cv x) R (.cv y)) p0015
  have p0017 :=
    @g_n_2exbidv (.classEq (.cv w) (syn_csn B))
      (syn_w3a (.classEq (.cv x) A) (.classEq (.cv w) (syn_csn (.cv y)))
        (syn_wbr (.cv x) R (.cv y)))
      (syn_w3a (.classEq (.cv x) A) (.classEq (.cv y) B) (syn_wbr (.cv x) R (.cv y))) x y
      dv_cache_0003 dv_cache_0004 p0016
  have p0018 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_si z w x y R
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
      dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
  have p0019 :=
    @g_brab
      (syn_wex x (syn_wex y (syn_w3a (.classEq (.cv z) (syn_csn (.cv x)))
            (.classEq (.cv w) (syn_csn (.cv y))) (syn_wbr (.cv x) R (.cv y)))))
      (syn_wex x (syn_wex y (syn_w3a (.classEq (.cv x) A) (.classEq (.cv w) (syn_csn (.cv y)))
            (syn_wbr (.cv x) R (.cv y)))))
      (syn_wex x (syn_wex y (syn_w3a (.classEq (.cv x) A) (.classEq (.cv y) B)
            (syn_wbr (.cv x) R (.cv y)))))
      z w (syn_csn A) (syn_csn B) (syn_csi R) dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0012 p0000 p0001 p0009 p0017
      p0018
  have p0020 := @g_breq1 (.cv x) A (.cv y) R
  have p0021 := @g_breq2 (.cv y) B A R
  have p0022 :=
    @g_ceqsex2v (syn_wbr (.cv x) R (.cv y)) (syn_wbr A R (.cv y)) (syn_wbr A R B) x y A B
      dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026
      dv_cache_0027 hyp_brsnsi_1 hyp_brsnsi_2 p0020 p0021
  have p0023 :=
    @g_bitri (syn_wbr (syn_csn A) (syn_csi R) (syn_csn B))
      (syn_wex x (syn_wex y (syn_w3a (.classEq (.cv x) A) (.classEq (.cv y) B)
            (syn_wbr (.cv x) R (.cv y)))))
      (syn_wbr A R B) p0019 p0022
  exact p0023

@[expose]
noncomputable def g_opsnelsi (A : Class) (B : Class) (R : Class)
    (hyp_brsnsi_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_brsnsi_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf
      (syn_wb (.classMem (syn_cop (syn_csn A) (syn_csn B)) (syn_csi R))
        (.classMem (syn_cop A B) R)) :=
  by
  have p0000 := @g_brsnsi A B R hyp_brsnsi_1 hyp_brsnsi_2
  have p0001 := (Nominal.biimpRefl (syn_wbr (syn_csn A) (syn_csi R) (syn_csn B)))
  have p0002 := (Nominal.biimpRefl (syn_wbr A R B))
  have p0003 :=
    @g_n_3bitr3i (syn_wbr (syn_csn A) (syn_csi R) (syn_csn B)) (syn_wbr A R B)
      (.classMem (syn_cop (syn_csn A) (syn_csn B)) (syn_csi R))
      (.classMem (syn_cop A B) R) p0000 p0001 p0002
  exact p0003

@[expose]
noncomputable def g_brsnsi1 (x : Var) (A : Class) (B : Class) (R : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_R_x : x ∉ R.fv)
    (hyp_brsnsi1_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf
      (syn_wb (syn_wbr (syn_csn A) (syn_csi R) B)
        (syn_wex x (syn_wa (.classEq B (syn_csn (.cv x))) (syn_wbr A R (.cv x))))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv ∪ R.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have dv_cache_0001 : y ∉ ((syn_csn A)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, fresh_y_not_A,
          not_false_eq_true])
  have dv_cache_0002 : x ∉ ((syn_csn A)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, dv_A_x,
          not_false_eq_true])
  have dv_cache_0003 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_B, not_false_eq_true])
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
  have dv_cache_0005 : y ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_R, not_false_eq_true])
  have dv_cache_0006 : x ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_x, not_false_eq_true])
  have dv_cache_0007 : y ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show y ≠ x from (by exact fresh_y_ne_x))
  have dv_cache_0008 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0009 :
    y ∉ ((syn_wa (.classEq B (syn_csn (.cv x))) (syn_wbr A R (.cv x)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          Finset.mem_singleton, fresh_y_not_B, fresh_y_ne_x, fresh_y_not_A, fresh_y_not_R,
          or_false, not_false_eq_true])
  have p0000 :=
    @g_brsi y x (syn_csn A) B R dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0001 :=
    @g_excom
      (syn_w3a (.classEq (syn_csn A) (syn_csn (.cv y))) (.classEq B (syn_csn (.cv x)))
        (syn_wbr (.cv y) R (.cv x)))
      y x
  have p0002 := @g_eqcom (syn_csn A) (syn_csn (.cv y))
  have p0003 := @g_vex y
  have p0004 := @g_sneqb (.cv y) A p0003
  have p0005 :=
    @g_bitri (.classEq (syn_csn A) (syn_csn (.cv y)))
      (.classEq (syn_csn (.cv y)) (syn_csn A)) (.classEq (.cv y) A) p0002 p0004
  have p0006 :=
    @g_n_3anbi1i (.classEq (syn_csn A) (syn_csn (.cv y))) (.classEq (.cv y) A)
      (.classEq B (syn_csn (.cv x))) (syn_wbr (.cv y) R (.cv x)) p0005
  have p0007 :=
    @g_n_3anass (.classEq (.cv y) A) (.classEq B (syn_csn (.cv x)))
      (syn_wbr (.cv y) R (.cv x))
  have p0008 :=
    @g_bitri
      (syn_w3a (.classEq (syn_csn A) (syn_csn (.cv y))) (.classEq B (syn_csn (.cv x)))
        (syn_wbr (.cv y) R (.cv x)))
      (syn_w3a (.classEq (.cv y) A) (.classEq B (syn_csn (.cv x))) (syn_wbr (.cv y) R (.cv x)))
      (syn_wa (.classEq (.cv y) A)
        (syn_wa (.classEq B (syn_csn (.cv x))) (syn_wbr (.cv y) R (.cv x))))
      p0006 p0007
  have p0009 :=
    @g_exbii
      (syn_w3a (.classEq (syn_csn A) (syn_csn (.cv y))) (.classEq B (syn_csn (.cv x)))
        (syn_wbr (.cv y) R (.cv x)))
      (syn_wa (.classEq (.cv y) A)
        (syn_wa (.classEq B (syn_csn (.cv x))) (syn_wbr (.cv y) R (.cv x))))
      y p0008
  have p0010 := @g_breq1 (.cv y) A (.cv x) R
  have p0011 :=
    @g_anbi2d (.classEq (.cv y) A) (syn_wbr (.cv y) R (.cv x)) (syn_wbr A R (.cv x))
      (.classEq B (syn_csn (.cv x))) p0010
  have p0012 :=
    @g_ceqsexv (syn_wa (.classEq B (syn_csn (.cv x))) (syn_wbr (.cv y) R (.cv x)))
      (syn_wa (.classEq B (syn_csn (.cv x))) (syn_wbr A R (.cv x))) y A dv_cache_0008
      dv_cache_0009 hyp_brsnsi1_1 p0011
  have p0013 :=
    @g_bitri
      (syn_wex y
        (syn_w3a (.classEq (syn_csn A) (syn_csn (.cv y))) (.classEq B (syn_csn (.cv x)))
          (syn_wbr (.cv y) R (.cv x))))
      (syn_wex y (syn_wa (.classEq (.cv y) A)
          (syn_wa (.classEq B (syn_csn (.cv x))) (syn_wbr (.cv y) R (.cv x)))))
      (syn_wa (.classEq B (syn_csn (.cv x))) (syn_wbr A R (.cv x))) p0009 p0012
  have p0014 :=
    @g_exbii
      (syn_wex y
        (syn_w3a (.classEq (syn_csn A) (syn_csn (.cv y))) (.classEq B (syn_csn (.cv x)))
          (syn_wbr (.cv y) R (.cv x))))
      (syn_wa (.classEq B (syn_csn (.cv x))) (syn_wbr A R (.cv x))) x p0013
  have p0015 :=
    @g_bitri
      (syn_wex y (syn_wex x
          (syn_w3a (.classEq (syn_csn A) (syn_csn (.cv y))) (.classEq B (syn_csn (.cv x)))
            (syn_wbr (.cv y) R (.cv x)))))
      (syn_wex x (syn_wex y
          (syn_w3a (.classEq (syn_csn A) (syn_csn (.cv y))) (.classEq B (syn_csn (.cv x)))
            (syn_wbr (.cv y) R (.cv x)))))
      (syn_wex x (syn_wa (.classEq B (syn_csn (.cv x))) (syn_wbr A R (.cv x)))) p0001
      p0014
  have p0016 :=
    @g_bitri (syn_wbr (syn_csn A) (syn_csi R) B)
      (syn_wex y (syn_wex x
          (syn_w3a (.classEq (syn_csn A) (syn_csn (.cv y))) (.classEq B (syn_csn (.cv x)))
            (syn_wbr (.cv y) R (.cv x)))))
      (syn_wex x (syn_wa (.classEq B (syn_csn (.cv x))) (syn_wbr A R (.cv x)))) p0000
      p0015
  exact p0016

@[expose]
noncomputable def g_brsnsi2 (x : Var) (A : Class) (B : Class) (R : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_R_x : x ∉ R.fv)
    (hyp_brsnsi1_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf
      (syn_wb (syn_wbr B (syn_csi R) (syn_csn A))
        (syn_wex x (syn_wa (.classEq B (syn_csn (.cv x))) (syn_wbr (.cv x) R A)))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv ∪ R.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ (B).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_x, not_false_eq_true])
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
  have dv_cache_0003 : x ∉ ((syn_csn A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, dv_A_x,
          not_false_eq_true])
  have dv_cache_0004 : y ∉ ((syn_csn A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, fresh_y_not_A,
          not_false_eq_true])
  have dv_cache_0005 : x ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_x, not_false_eq_true])
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
  have dv_cache_0007 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0008 : y ∉ ((Wff.classEq B (syn_csn (.cv x)))).fv :=
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_not_B, fresh_y_ne_x, or_false, not_false_eq_true])
  have dv_cache_0009 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0010 : y ∉ ((syn_wbr (.cv x) R A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_x, fresh_y_not_A, fresh_y_not_R, or_false,
          not_false_eq_true])
  have p0000 :=
    @g_brsi x y B (syn_csn A) R dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0001 :=
    @g_n_3anass (.classEq B (syn_csn (.cv x))) (.classEq (syn_csn A) (syn_csn (.cv y)))
      (syn_wbr (.cv x) R (.cv y))
  have p0002 :=
    @g_exbii
      (syn_w3a (.classEq B (syn_csn (.cv x))) (.classEq (syn_csn A) (syn_csn (.cv y)))
        (syn_wbr (.cv x) R (.cv y)))
      (syn_wa (.classEq B (syn_csn (.cv x)))
        (syn_wa (.classEq (syn_csn A) (syn_csn (.cv y))) (syn_wbr (.cv x) R (.cv y))))
      y p0001
  have p0003 :=
    @g_n_19_42v (.classEq B (syn_csn (.cv x)))
      (syn_wa (.classEq (syn_csn A) (syn_csn (.cv y))) (syn_wbr (.cv x) R (.cv y))) y
      dv_cache_0008
  have p0004 := @g_sneqb A (.cv y) hyp_brsnsi1_1
  have p0005 := @g_eqcom A (.cv y)
  have p0006 :=
    @g_bitri (.classEq (syn_csn A) (syn_csn (.cv y))) (.classEq A (.cv y))
      (.classEq (.cv y) A) p0004 p0005
  have p0007 :=
    @g_anbi1i (.classEq (syn_csn A) (syn_csn (.cv y))) (.classEq (.cv y) A)
      (syn_wbr (.cv x) R (.cv y)) p0006
  have p0008 :=
    @g_exbii (syn_wa (.classEq (syn_csn A) (syn_csn (.cv y))) (syn_wbr (.cv x) R (.cv y)))
      (syn_wa (.classEq (.cv y) A) (syn_wbr (.cv x) R (.cv y))) y p0007
  have p0009 := @g_breq2 (.cv y) A (.cv x) R
  have p0010 :=
    @g_ceqsexv (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv x) R A) y A dv_cache_0009
      dv_cache_0010 hyp_brsnsi1_1 p0009
  have p0011 :=
    @g_bitri
      (syn_wex y (syn_wa (.classEq (syn_csn A) (syn_csn (.cv y))) (syn_wbr (.cv x) R (.cv y))))
      (syn_wex y (syn_wa (.classEq (.cv y) A) (syn_wbr (.cv x) R (.cv y))))
      (syn_wbr (.cv x) R A) p0008 p0010
  have p0012 :=
    @g_anbi2i
      (syn_wex y (syn_wa (.classEq (syn_csn A) (syn_csn (.cv y))) (syn_wbr (.cv x) R (.cv y))))
      (syn_wbr (.cv x) R A) (.classEq B (syn_csn (.cv x))) p0011
  have p0013 :=
    @g_bitri
      (syn_wex y (syn_wa (.classEq B (syn_csn (.cv x)))
          (syn_wa (.classEq (syn_csn A) (syn_csn (.cv y))) (syn_wbr (.cv x) R (.cv y)))))
      (syn_wa (.classEq B (syn_csn (.cv x))) (syn_wex y
          (syn_wa (.classEq (syn_csn A) (syn_csn (.cv y))) (syn_wbr (.cv x) R (.cv y)))))
      (syn_wa (.classEq B (syn_csn (.cv x))) (syn_wbr (.cv x) R A)) p0003 p0012
  have p0014 :=
    @g_bitri
      (syn_wex y
        (syn_w3a (.classEq B (syn_csn (.cv x))) (.classEq (syn_csn A) (syn_csn (.cv y)))
          (syn_wbr (.cv x) R (.cv y))))
      (syn_wex y (syn_wa (.classEq B (syn_csn (.cv x)))
          (syn_wa (.classEq (syn_csn A) (syn_csn (.cv y))) (syn_wbr (.cv x) R (.cv y)))))
      (syn_wa (.classEq B (syn_csn (.cv x))) (syn_wbr (.cv x) R A)) p0002 p0013
  have p0015 :=
    @g_exbii
      (syn_wex y
        (syn_w3a (.classEq B (syn_csn (.cv x))) (.classEq (syn_csn A) (syn_csn (.cv y)))
          (syn_wbr (.cv x) R (.cv y))))
      (syn_wa (.classEq B (syn_csn (.cv x))) (syn_wbr (.cv x) R A)) x p0014
  have p0016 :=
    @g_bitri (syn_wbr B (syn_csi R) (syn_csn A))
      (syn_wex x (syn_wex y
          (syn_w3a (.classEq B (syn_csn (.cv x))) (.classEq (syn_csn A) (syn_csn (.cv y)))
            (syn_wbr (.cv x) R (.cv y)))))
      (syn_wex x (syn_wa (.classEq B (syn_csn (.cv x))) (syn_wbr (.cv x) R A))) p0000
      p0015
  exact p0016

@[expose]
noncomputable def g_brco1st (A : Class) (B : Class) (C : Class) (R : Class)
    (hyp_brco1st_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_brco1st_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf
      (syn_wb (syn_wbr (syn_cop A B) (syn_ccom R (syn_c1st)) C) (syn_wbr A R C)) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ R.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ ((syn_cop A B)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ (C).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_C, not_false_eq_true])
  have dv_cache_0003 : x ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_R, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((syn_c1st)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          compact_fv_not_mem_empty, not_false_eq_true])
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
  have dv_cache_0006 : x ∉ ((syn_wbr A R C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_C, fresh_x_not_R, or_false, not_false_eq_true])
  have p0000 :=
    @g_brco x (syn_cop A B) C R (syn_c1st) dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004
  have p0001 := @g_opbr1st A B (.cv x) hyp_brco1st_1 hyp_brco1st_2
  have p0002 := @g_eqcom A (.cv x)
  have p0003 :=
    @g_bitri (syn_wbr (syn_cop A B) (syn_c1st) (.cv x)) (.classEq A (.cv x))
      (.classEq (.cv x) A) p0001 p0002
  have p0004 :=
    @g_anbi1i (syn_wbr (syn_cop A B) (syn_c1st) (.cv x)) (.classEq (.cv x) A)
      (syn_wbr (.cv x) R C) p0003
  have p0005 :=
    @g_exbii (syn_wa (syn_wbr (syn_cop A B) (syn_c1st) (.cv x)) (syn_wbr (.cv x) R C))
      (syn_wa (.classEq (.cv x) A) (syn_wbr (.cv x) R C)) x p0004
  have p0006 := @g_breq1 (.cv x) A C R
  have p0007 :=
    @g_ceqsexv (syn_wbr (.cv x) R C) (syn_wbr A R C) x A dv_cache_0005 dv_cache_0006
      hyp_brco1st_1 p0006
  have p0008 :=
    @g_n_3bitri (syn_wbr (syn_cop A B) (syn_ccom R (syn_c1st)) C)
      (syn_wex x (syn_wa (syn_wbr (syn_cop A B) (syn_c1st) (.cv x)) (syn_wbr (.cv x) R C)))
      (syn_wex x (syn_wa (.classEq (.cv x) A) (syn_wbr (.cv x) R C))) (syn_wbr A R C)
      p0000 p0005 p0007
  exact p0008

@[expose]
noncomputable def g_brco2nd (A : Class) (B : Class) (C : Class) (R : Class)
    (hyp_brco1st_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_brco1st_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf
      (syn_wb (syn_wbr (syn_cop A B) (syn_ccom R (syn_c2nd)) C) (syn_wbr B R C)) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ R.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ ((syn_cop A B)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ (C).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_C, not_false_eq_true])
  have dv_cache_0003 : x ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_R, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((syn_c2nd)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0005 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_B, not_false_eq_true])
  have dv_cache_0006 : x ∉ ((syn_wbr B R C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          fresh_x_not_B, fresh_x_not_C, fresh_x_not_R, or_false, not_false_eq_true])
  have p0000 :=
    @g_brco x (syn_cop A B) C R (syn_c2nd) dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004
  have p0001 := @g_opbr2nd A B (.cv x) hyp_brco1st_1 hyp_brco1st_2
  have p0002 := @g_eqcom B (.cv x)
  have p0003 :=
    @g_bitri (syn_wbr (syn_cop A B) (syn_c2nd) (.cv x)) (.classEq B (.cv x))
      (.classEq (.cv x) B) p0001 p0002
  have p0004 :=
    @g_anbi1i (syn_wbr (syn_cop A B) (syn_c2nd) (.cv x)) (.classEq (.cv x) B)
      (syn_wbr (.cv x) R C) p0003
  have p0005 :=
    @g_exbii (syn_wa (syn_wbr (syn_cop A B) (syn_c2nd) (.cv x)) (syn_wbr (.cv x) R C))
      (syn_wa (.classEq (.cv x) B) (syn_wbr (.cv x) R C)) x p0004
  have p0006 := @g_breq1 (.cv x) B C R
  have p0007 :=
    @g_ceqsexv (syn_wbr (.cv x) R C) (syn_wbr B R C) x B dv_cache_0005 dv_cache_0006
      hyp_brco1st_2 p0006
  have p0008 :=
    @g_n_3bitri (syn_wbr (syn_cop A B) (syn_ccom R (syn_c2nd)) C)
      (syn_wex x (syn_wa (syn_wbr (syn_cop A B) (syn_c2nd) (.cv x)) (syn_wbr (.cv x) R C)))
      (syn_wex x (syn_wa (.classEq (.cv x) B) (syn_wbr (.cv x) R C))) (syn_wbr B R C)
      p0000 p0005 p0007
  exact p0008

@[expose]
noncomputable def g_txpeq2 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_ctxp C A) (syn_ctxp C B))) :=
  by
  have p0000 := @g_coeq2 A B (syn_ccnv (syn_c2nd))
  have p0001 :=
    @g_ineq2d (.classEq A B) (syn_ccom (syn_ccnv (syn_c2nd)) A)
      (syn_ccom (syn_ccnv (syn_c2nd)) B) (syn_ccom (syn_ccnv (syn_c1st)) C) p0000
  have p0002 := (Nominal.classEqRefl (syn_ctxp C A))
  have p0003 := (Nominal.classEqRefl (syn_ctxp C B))
  have p0004 :=
    @g_n_3eqtr4g (.classEq A B)
      (syn_cin (syn_ccom (syn_ccnv (syn_c1st)) C) (syn_ccom (syn_ccnv (syn_c2nd)) A))
      (syn_cin (syn_ccom (syn_ccnv (syn_c1st)) C) (syn_ccom (syn_ccnv (syn_c2nd)) B))
      (syn_ctxp C A) (syn_ctxp C B) p0001 p0002 p0003
  exact p0004


end NFChoice.DirectNominalPrf.WPPReplay

end

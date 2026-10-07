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

/-- Checked nominal proof certificate identified upstream as `g_cbvmpt`. -/
@[expose]
noncomputable def gCbvmpt (x : Var) (y : Var) (A : Class) (B : Class) (C : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (hyp_cbvmpt_1 : Nominal.NPrf (synWnfc y B))
    (hyp_cbvmpt_2 : Nominal.NPrf (synWnfc x C))
    (hyp_cbvmpt_3 : Nominal.NPrf (.imp (.objEq x y) (.classEq B C))) :
    Nominal.NPrf (.classEq (synCmpt x A B) (synCmpt y A C)) :=
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
  have dv_cache_0001 : w ∉ ((synWa (.classMem (.cv x) A) (.classEq (.cv z) B))).fv := by
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
  have dv_cache_0009 : w ∉ ((synWa (.classMem (.cv y) A) (.classEq (.cv z) C))).fv :=
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
  have p0000 := @gNfv (synWa (.classMem (.cv x) A) (.classEq (.cv z) B)) w dv_cache_0001
  have p0001 := @gNfv (.classMem (.cv w) A) x dv_cache_0002
  have p0002 := @gNfs1v (.classEq (.cv z) B) x w dv_cache_0003
  have p0003 :=
    @gNfan (.classMem (.cv w) A) (synWsb w x (.classEq (.cv z) B)) x p0001 p0002
  have p0004 := @gEleq1 (.cv x) (.cv w) A
  have p0005 := @gSbequ12 (.classEq (.cv z) B) x w
  have p0006_e01_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv x) (.cv w))
        (synWb (.classEq (.cv z) B) (synWsb w x (.classEq (.cv z) B)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWsb synWa synWex
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0005
  have p0006 :=
    @gAnbi12d (.classEq (.cv x) (.cv w)) (.classMem (.cv x) A) (.classMem (.cv w) A)
      (.classEq (.cv z) B) (synWsb w x (.classEq (.cv z) B)) p0004 p0006_e01_recanon
  have p0007_e02_recanon :
    Nominal.NPrf
      (.imp (.objEq x w) (synWb (synWa (.classMem (.cv x) A) (.classEq (.cv z) B))
          (synWa (.classMem (.cv w) A) (synWsb w x (.classEq (.cv z) B))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWa
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0006
  have p0007 :=
    @gCbvopab1 (synWa (.classMem (.cv x) A) (.classEq (.cv z) B))
      (synWa (.classMem (.cv w) A) (synWsb w x (.classEq (.cv z) B))) x z w
      dv_cache_0004 dv_cache_0005 p0000 p0003 p0007_e02_recanon
  have p0008 := @gNfv (.classMem (.cv w) A) y dv_cache_0006
  have p0009 := @gNfeq2 y (.cv z) B dv_cache_0007 hyp_cbvmpt_1
  have p0010 := @gNfsb (.classEq (.cv z) B) x w y dv_cache_0008 p0009
  have p0011 :=
    @gNfan (.classMem (.cv w) A) (synWsb w x (.classEq (.cv z) B)) y p0008 p0010
  have p0012 := @gNfv (synWa (.classMem (.cv y) A) (.classEq (.cv z) C)) w dv_cache_0009
  have p0013 := @gEleq1 (.cv w) (.cv y) A
  have p0014 := @gSbequ (.classEq (.cv z) B) w y x
  have p0015 := @gNfeq2 x (.cv z) C dv_cache_0010 hyp_cbvmpt_2
  have p0016_e00_recanon :
    Nominal.NPrf (.imp (.classEq (.cv x) (.cv y)) (.classEq B C)) :=
    Nominal.RecanonTransportDev.transport
      (by
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      hyp_cbvmpt_3
  have p0016 := @gEqeq2d (.classEq (.cv x) (.cv y)) B C (.cv z) p0016_e00_recanon
  have p0017_e01_recanon :
    Nominal.NPrf (.imp (.objEq x y) (synWb (.classEq (.cv z) B) (.classEq (.cv z) C))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0016
  have p0017 :=
    @gSbie (.classEq (.cv z) B) (.classEq (.cv z) C) x y p0015 p0017_e01_recanon
  have p0018_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv w) (.cv y))
        (synWb (synWsb w x (.classEq (.cv z) B)) (synWsb y x (.classEq (.cv z) B)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWsb synWa synWex
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0014
  have p0018 :=
    @gSyl6bb (.classEq (.cv w) (.cv y)) (synWsb w x (.classEq (.cv z) B))
      (synWsb y x (.classEq (.cv z) B)) (.classEq (.cv z) C) p0018_e00_recanon p0017
  have p0019 :=
    @gAnbi12d (.classEq (.cv w) (.cv y)) (.classMem (.cv w) A) (.classMem (.cv y) A)
      (synWsb w x (.classEq (.cv z) B)) (.classEq (.cv z) C) p0013 p0018
  have p0020_e02_recanon :
    Nominal.NPrf
      (.imp (.objEq w y)
        (synWb (synWa (.classMem (.cv w) A) (synWsb w x (.classEq (.cv z) B)))
          (synWa (.classMem (.cv y) A) (.classEq (.cv z) C)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWa synWsb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0019
  have p0020 :=
    @gCbvopab1 (synWa (.classMem (.cv w) A) (synWsb w x (.classEq (.cv z) B)))
      (synWa (.classMem (.cv y) A) (.classEq (.cv z) C)) w z y dv_cache_0011
      dv_cache_0012 p0011 p0012 p0020_e02_recanon
  have p0021 :=
    @gEqtri (synCopab x z (synWa (.classMem (.cv x) A) (.classEq (.cv z) B)))
      (synCopab w z (synWa (.classMem (.cv w) A) (synWsb w x (.classEq (.cv z) B))))
      (synCopab y z (synWa (.classMem (.cv y) A) (.classEq (.cv z) C))) p0007 p0020
  have p0022 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfMpt x z A B
      dv_cache_0013 dv_cache_0014 dv_cache_0004
  have p0023 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfMpt y z A C
      dv_cache_0013 dv_cache_0015 dv_cache_0016
  have p0024 :=
    @gN3eqtr4i (synCopab x z (synWa (.classMem (.cv x) A) (.classEq (.cv z) B)))
      (synCopab y z (synWa (.classMem (.cv y) A) (.classEq (.cv z) C))) (synCmpt x A B)
      (synCmpt y A C) p0021 p0022 p0023
  exact p0024

/-- Checked nominal proof certificate identified upstream as `g_cbvmptv`. -/
@[expose]
noncomputable def gCbvmptv (x : Var) (y : Var) (A : Class) (B : Class) (C : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_y : y ∉ B.fv) (dv_C_x : x ∉ C.fv)
    (hyp_cbvmptv_1 : Nominal.NPrf (.imp (.objEq x y) (.classEq B C))) :
    Nominal.NPrf (.classEq (synCmpt x A B) (synCmpt y A C)) :=
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
  have p0000 := @gNfcv y B dv_cache_0001
  have p0001 := @gNfcv x C dv_cache_0002
  have p0002 := @gCbvmpt x y A B C dv_cache_0003 dv_cache_0004 p0000 p0001 hyp_cbvmptv_1
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_mptpreima`. -/
@[expose]
noncomputable def gMptpreima (x : Var) (A : Class) (B : Class) (C : Class) (F : Class)
    (dv_C_x : x ∉ C.fv) (hyp_dmmpt2_1 : Nominal.NPrf (.classEq F (synCmpt x A B))) :
    Nominal.NPrf (.classEq (synCima (synCcnv F) C) (synCrab x A (.classMem B C))) :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfMpt x y A B
      dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    @gEqtri F (synCmpt x A B)
      (synCopab x y (synWa (.classMem (.cv x) A) (.classEq (.cv y) B))) hyp_dmmpt2_1
      p0000
  have p0002 :=
    @gCnveqi F (synCopab x y (synWa (.classMem (.cv x) A) (.classEq (.cv y) B))) p0001
  have p0003 :=
    @gCnvopab (synWa (.classMem (.cv x) A) (.classEq (.cv y) B)) x y dv_cache_0003
  have p0004 :=
    @gEqtri (synCcnv F)
      (synCcnv (synCopab x y (synWa (.classMem (.cv x) A) (.classEq (.cv y) B))))
      (synCopab y x (synWa (.classMem (.cv x) A) (.classEq (.cv y) B))) p0002 p0003
  have p0005 :=
    @gImaeq1i (synCcnv F)
      (synCopab y x (synWa (.classMem (.cv x) A) (.classEq (.cv y) B))) C p0004
  have p0006 :=
    @gDfima3 (synCopab y x (synWa (.classMem (.cv x) A) (.classEq (.cv y) B))) C
  have p0007 :=
    @gResopab (synWa (.classMem (.cv x) A) (.classEq (.cv y) B)) y x C dv_cache_0004
      dv_cache_0005 dv_cache_0006
  have p0008 :=
    @gRneqi
      (synCres (synCopab y x (synWa (.classMem (.cv x) A) (.classEq (.cv y) B))) C)
      (synCopab y x (synWa (.classMem (.cv y) C)
          (synWa (.classMem (.cv x) A) (.classEq (.cv y) B))))
      p0007
  have p0009 :=
    @gAncom (.classMem (.cv y) C) (synWa (.classMem (.cv x) A) (.classEq (.cv y) B))
  have p0010 := @gAnass (.classMem (.cv x) A) (.classEq (.cv y) B) (.classMem (.cv y) C)
  have p0011 :=
    @gBitri
      (synWa (.classMem (.cv y) C) (synWa (.classMem (.cv x) A) (.classEq (.cv y) B)))
      (synWa (synWa (.classMem (.cv x) A) (.classEq (.cv y) B)) (.classMem (.cv y) C))
      (synWa (.classMem (.cv x) A) (synWa (.classEq (.cv y) B) (.classMem (.cv y) C)))
      p0009 p0010
  have p0012 :=
    @gExbii
      (synWa (.classMem (.cv y) C) (synWa (.classMem (.cv x) A) (.classEq (.cv y) B)))
      (synWa (.classMem (.cv x) A) (synWa (.classEq (.cv y) B) (.classMem (.cv y) C))) y
      p0011
  have p0013 :=
    @gN1942v (.classMem (.cv x) A) (synWa (.classEq (.cv y) B) (.classMem (.cv y) C))
      y dv_cache_0007
  have p0014 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClelOfDV y B C
      dv_cache_0002 dv_cache_0004)
  have p0015 :=
    @gBicomi (.classMem B C)
      (synWex y (synWa (.classEq (.cv y) B) (.classMem (.cv y) C))) p0014
  have p0016 :=
    @gAnbi2i (synWex y (synWa (.classEq (.cv y) B) (.classMem (.cv y) C)))
      (.classMem B C) (.classMem (.cv x) A) p0015
  have p0017 :=
    @gBitri
      (synWex y (synWa (.classMem (.cv x) A)
          (synWa (.classEq (.cv y) B) (.classMem (.cv y) C))))
      (synWa (.classMem (.cv x) A)
        (synWex y (synWa (.classEq (.cv y) B) (.classMem (.cv y) C))))
      (synWa (.classMem (.cv x) A) (.classMem B C)) p0013 p0016
  have p0018 :=
    @gBitri
      (synWex y (synWa (.classMem (.cv y) C)
          (synWa (.classMem (.cv x) A) (.classEq (.cv y) B))))
      (synWex y (synWa (.classMem (.cv x) A)
          (synWa (.classEq (.cv y) B) (.classMem (.cv y) C))))
      (synWa (.classMem (.cv x) A) (.classMem B C)) p0012 p0017
  have p0019 :=
    @gAbbii
      (synWex y (synWa (.classMem (.cv y) C)
          (synWa (.classMem (.cv x) A) (.classEq (.cv y) B))))
      (synWa (.classMem (.cv x) A) (.classMem B C)) x p0018
  have p0020 :=
    @gRnopab
      (synWa (.classMem (.cv y) C) (synWa (.classMem (.cv x) A) (.classEq (.cv y) B))) y
      x dv_cache_0006
  have p0021 := (Nominal.classEqRefl (synCrab x A (.classMem B C)))
  have p0022 :=
    @gN3eqtr4i
      (.cab x (synWex y (synWa (.classMem (.cv y) C)
            (synWa (.classMem (.cv x) A) (.classEq (.cv y) B)))))
      (.cab x (synWa (.classMem (.cv x) A) (.classMem B C)))
      (synCrn (synCopab y x (synWa (.classMem (.cv y) C)
            (synWa (.classMem (.cv x) A) (.classEq (.cv y) B)))))
      (synCrab x A (.classMem B C)) p0019 p0020 p0021
  have p0023 :=
    @gEqtri
      (synCrn (synCres (synCopab y x (synWa (.classMem (.cv x) A) (.classEq (.cv y) B))) C))
      (synCrn (synCopab y x (synWa (.classMem (.cv y) C)
            (synWa (.classMem (.cv x) A) (.classEq (.cv y) B)))))
      (synCrab x A (.classMem B C)) p0008 p0022
  have p0024 :=
    @gEqtri
      (synCima (synCopab y x (synWa (.classMem (.cv x) A) (.classEq (.cv y) B))) C)
      (synCrn (synCres (synCopab y x (synWa (.classMem (.cv x) A) (.classEq (.cv y) B))) C))
      (synCrab x A (.classMem B C)) p0006 p0023
  have p0025 :=
    @gEqtri (synCima (synCcnv F) C)
      (synCima (synCopab y x (synWa (.classMem (.cv x) A) (.classEq (.cv y) B))) C)
      (synCrab x A (.classMem B C)) p0005 p0024
  exact p0025

/-- Checked nominal proof certificate identified upstream as `g_dmmpt`. -/
@[expose]
noncomputable def gDmmpt (x : Var) (A : Class) (B : Class) (F : Class)
    (hyp_dmmpt2_1 : Nominal.NPrf (.classEq F (synCmpt x A B))) :
    Nominal.NPrf (.classEq (synCdm F) (synCrab x A (.classMem B (synCvv)))) :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfMpt x y A B
      dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    @gEqtri F (synCmpt x A B)
      (synCopab x y (synWa (.classMem (.cv x) A) (.classEq (.cv y) B))) hyp_dmmpt2_1
      p0000
  have p0002 :=
    @gDmeqi F (synCopab x y (synWa (.classMem (.cv x) A) (.classEq (.cv y) B))) p0001
  have p0003 :=
    @gDmopab (synWa (.classMem (.cv x) A) (.classEq (.cv y) B)) x y dv_cache_0003
  have p0004 := @gN1942v (.classMem (.cv x) A) (.classEq (.cv y) B) y dv_cache_0004
  have p0005 := @gIsset y B dv_cache_0002
  have p0006 :=
    @gAnbi2i (.classMem B (synCvv)) (synWex y (.classEq (.cv y) B))
      (.classMem (.cv x) A) p0005
  have p0007 :=
    @gBitr4i (synWex y (synWa (.classMem (.cv x) A) (.classEq (.cv y) B)))
      (synWa (.classMem (.cv x) A) (synWex y (.classEq (.cv y) B)))
      (synWa (.classMem (.cv x) A) (.classMem B (synCvv))) p0004 p0006
  have p0008 :=
    @gAbbii (synWex y (synWa (.classMem (.cv x) A) (.classEq (.cv y) B)))
      (synWa (.classMem (.cv x) A) (.classMem B (synCvv))) x p0007
  have p0009 := (Nominal.classEqRefl (synCrab x A (.classMem B (synCvv))))
  have p0010 :=
    @gEqtr4i (.cab x (synWex y (synWa (.classMem (.cv x) A) (.classEq (.cv y) B))))
      (.cab x (synWa (.classMem (.cv x) A) (.classMem B (synCvv))))
      (synCrab x A (.classMem B (synCvv))) p0008 p0009
  have p0011 :=
    @gN3eqtri (synCdm F)
      (synCdm (synCopab x y (synWa (.classMem (.cv x) A) (.classEq (.cv y) B))))
      (.cab x (synWex y (synWa (.classMem (.cv x) A) (.classEq (.cv y) B))))
      (synCrab x A (.classMem B (synCvv))) p0002 p0003 p0010
  exact p0011

/-- Checked nominal proof certificate identified upstream as `g_rnmpt`. -/
@[expose]
noncomputable def gRnmpt (x : Var) (y : Var) (A : Class) (B : Class) (F : Class)
    (dv_A_y : y ∉ A.fv) (dv_B_y : y ∉ B.fv) (dv_x_y : x ≠ y)
    (hyp_rnmpt_1 : Nominal.NPrf (.classEq F (synCmpt x A B))) :
    Nominal.NPrf (.classEq (synCrn F) (.cab y (synWrex x A (.classEq (.cv y) B)))) :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfMpt x y A B
      dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    @gEqtri F (synCmpt x A B)
      (synCopab x y (synWa (.classMem (.cv x) A) (.classEq (.cv y) B))) hyp_rnmpt_1
      p0000
  have p0002 :=
    @gRneqi F (synCopab x y (synWa (.classMem (.cv x) A) (.classEq (.cv y) B))) p0001
  have p0003 := @gRnopab2 x y A B dv_cache_0003
  have p0004 :=
    @gEqtri (synCrn F)
      (synCrn (synCopab x y (synWa (.classMem (.cv x) A) (.classEq (.cv y) B))))
      (.cab y (synWrex x A (.classEq (.cv y) B))) p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_mptfng`. -/
@[expose]
noncomputable def gMptfng (x : Var) (A : Class) (B : Class) (F : Class)
    (dv_A_x : x ∉ A.fv) (hyp_mptfng_1 : Nominal.NPrf (.classEq F (synCmpt x A B))) :
    Nominal.NPrf (synWb (synWral x A (.classMem B (synCvv))) (synWfn F A)) :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfMpt x y A B
      dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    @gEqtri F (synCmpt x A B)
      (synCopab x y (synWa (.classMem (.cv x) A) (.classEq (.cv y) B))) hyp_mptfng_1
      p0000
  have p0002 :=
    @gFnopab2g x y A B F dv_cache_0004 dv_cache_0001 dv_cache_0002 dv_cache_0003 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_fnmpt`. -/
@[expose]
noncomputable def gFnmpt (x : Var) (A : Class) (B : Class) (F : Class) (V : Class)
    (dv_A_x : x ∉ A.fv) (hyp_mptfng_1 : Nominal.NPrf (.classEq F (synCmpt x A B))) :
    Nominal.NPrf (.imp (synWral x A (.classMem B V)) (synWfn F A)) :=
  by
  have dv_cache_0001 : x ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have p0000 := @gElex B V
  have p0001 := @gRalimi (.classMem B V) (.classMem B (synCvv)) x A p0000
  have p0002 := @gMptfng x A B F dv_cache_0001 hyp_mptfng_1
  have p0003 :=
    @gSylib (synWral x A (.classMem B V)) (synWral x A (.classMem B (synCvv)))
      (synWfn F A) p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_fnmpti`. -/
@[expose]
noncomputable def gFnmpti (x : Var) (A : Class) (B : Class) (F : Class)
    (dv_A_x : x ∉ A.fv) (hyp_fnmpti_1 : Nominal.NPrf (.classMem B (synCvv)))
    (hyp_fnmpti_2 : Nominal.NPrf (.classEq F (synCmpt x A B))) :
    Nominal.NPrf (synWfn F A) :=
  by
  have dv_cache_0001 : x ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have p0000 := @gRgenw (.classMem B (synCvv)) x A hyp_fnmpti_1
  have p0001 := @gMptfng x A B F dv_cache_0001 hyp_fnmpti_2
  have p0002 := @gMpbi (synWral x A (.classMem B (synCvv))) (synWfn F A) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_fmpt`. -/
@[expose]
noncomputable def gFmpt (x : Var) (A : Class) (B : Class) (C : Class) (F : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv)
    (hyp_fmpt_1 : Nominal.NPrf (.classEq F (synCmpt x A C))) :
    Nominal.NPrf (synWb (synWral x A (.classMem C B)) (synWf F A B)) :=
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
  have dv_cache_0007 : y ∉ ((synWral x A (.classMem C B))).fv :=
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
  have p0000 := @gFnmpt x A C F B dv_cache_0001 hyp_fmpt_1
  have p0001 := @gRnmpt x y A C F dv_cache_0002 dv_cache_0003 dv_cache_0004 hyp_fmpt_1
  have p0002 := @gR1929 (.classMem C B) (.classEq (.cv y) C) x A
  have p0003 := @gEleq1 (.cv y) C B
  have p0004 :=
    @gBiimparc (.classEq (.cv y) C) (.classMem (.cv y) B) (.classMem C B) p0003
  have p0005 :=
    @gRexlimivw (synWa (.classMem C B) (.classEq (.cv y) C)) (.classMem (.cv y) B) x A
      dv_cache_0005 p0004
  have p0006 :=
    @gSyl (synWa (synWral x A (.classMem C B)) (synWrex x A (.classEq (.cv y) C)))
      (synWrex x A (synWa (.classMem C B) (.classEq (.cv y) C))) (.classMem (.cv y) B)
      p0002 p0005
  have p0007 :=
    @gEx (synWral x A (.classMem C B)) (synWrex x A (.classEq (.cv y) C))
      (.classMem (.cv y) B) p0006
  have p0008 :=
    @gAbssdv (synWral x A (.classMem C B)) (synWrex x A (.classEq (.cv y) C)) y B
      dv_cache_0006 dv_cache_0007 p0007
  have p0009 :=
    @gSyl5eqss (synWral x A (.classMem C B)) (synCrn F)
      (.cab y (synWrex x A (.classEq (.cv y) C))) B p0001 p0008
  have p0010 := (Nominal.biimpRefl (synWf F A B))
  have p0011 :=
    @gSylanbrc (synWral x A (.classMem C B)) (synWfn F A) (synWss (synCrn F) B)
      (synWf F A B) p0000 p0009 p0010
  have p0012 := @gMptpreima x A C B F dv_cache_0008 hyp_fmpt_1
  have p0013 := @gFimacnv A B F
  have p0014 :=
    @gSyl5reqr (synWf F A B) (synCrab x A (.classMem C B)) (synCima (synCcnv F) B) A
      p0012 p0013
  have p0015 := @gRabid2 (.classMem C B) x A dv_cache_0001
  have p0016 :=
    @gSylib (synWf F A B) (.classEq A (synCrab x A (.classMem C B)))
      (synWral x A (.classMem C B)) p0014 p0015
  have p0017 := @gImpbii (synWral x A (.classMem C B)) (synWf F A B) p0011 p0016
  exact p0017

/-- Checked nominal proof certificate identified upstream as `g_fmpti`. -/
@[expose]
noncomputable def gFmpti (x : Var) (A : Class) (B : Class) (C : Class) (F : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv)
    (hyp_fmpt_1 : Nominal.NPrf (.classEq F (synCmpt x A C)))
    (hyp_fmpti_2 : Nominal.NPrf (.imp (.classMem (.cv x) A) (.classMem C B))) :
    Nominal.NPrf (synWf F A B) :=
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
  have p0000 := @gRgen (.classMem C B) x A hyp_fmpti_2
  have p0001 := @gFmpt x A B C F dv_cache_0001 dv_cache_0002 hyp_fmpt_1
  have p0002 := @gMpbi (synWral x A (.classMem C B)) (synWf F A B) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_resmpt`. -/
@[expose]
noncomputable def gResmpt (x : Var) (A : Class) (B : Class) (C : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf
      (.imp (synWss B A) (.classEq (synCres (synCmpt x A C) B) (synCmpt x B C))) :=
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
    @gResopab2 (.classEq (.cv y) C) x y B A dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005
  have p0001 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfMpt x y A C
      dv_cache_0004 dv_cache_0006 dv_cache_0005
  have p0002 :=
    @gReseq1i (synCmpt x A C)
      (synCopab x y (synWa (.classMem (.cv x) A) (.classEq (.cv y) C))) B p0001
  have p0003 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfMpt x y B C
      dv_cache_0002 dv_cache_0006 dv_cache_0005
  have p0004 :=
    @gN3eqtr4g (synWss B A)
      (synCres (synCopab x y (synWa (.classMem (.cv x) A) (.classEq (.cv y) C))) B)
      (synCopab x y (synWa (.classMem (.cv x) B) (.classEq (.cv y) C)))
      (synCres (synCmpt x A C) B) (synCmpt x B C) p0000 p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_fvmptg`. -/
@[expose]
noncomputable def gFvmptg (x : Var) (A : Class) (B : Class) (C : Class) (D : Class)
    (R : Class) (F : Class) (dv_A_x : x ∉ A.fv) (dv_C_x : x ∉ C.fv) (dv_D_x : x ∉ D.fv)
    (hyp_fvmptg_1 : Nominal.NPrf (.imp (.classEq (.cv x) A) (.classEq B C)))
    (hyp_fvmptg_2 : Nominal.NPrf (.classEq F (synCmpt x D B))) :
    Nominal.NPrf
      (.imp (synWa (.classMem A D) (.classMem C R)) (.classEq (synCfv F A) C)) :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfMpt x y D B
      dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    @gEqtri F (synCmpt x D B)
      (synCopab x y (synWa (.classMem (.cv x) D) (.classEq (.cv y) B))) hyp_fvmptg_2
      p0000
  have p0002 :=
    @gFvopab4g x y A B C D R F dv_cache_0004 dv_cache_0005 dv_cache_0002 dv_cache_0006
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

/-- Checked nominal proof certificate identified upstream as `g_fvmpti`. -/
@[expose]
noncomputable def gFvmpti (x : Var) (A : Class) (B : Class) (C : Class) (D : Class)
    (F : Class) (dv_A_x : x ∉ A.fv) (dv_C_x : x ∉ C.fv) (dv_D_x : x ∉ D.fv)
    (hyp_fvmptg_1 : Nominal.NPrf (.imp (.classEq (.cv x) A) (.classEq B C)))
    (hyp_fvmptg_2 : Nominal.NPrf (.classEq F (synCmpt x D B))) :
    Nominal.NPrf (.imp (.classMem A D) (.classEq (synCfv F A) (synCfv (synCid) C))) :=
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
  have dv_cache_0004 : x ∉ ((Wff.classMem C (synCvv))).fv :=
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
    @gFvmptg x A B C D (synCvv) F dv_cache_0001 dv_cache_0002 dv_cache_0003 hyp_fvmptg_1
      hyp_fvmptg_2
  have p0001 := @gFvi C (synCvv)
  have p0002 :=
    @gAdantl (.classMem C (synCvv)) (.classEq (synCfv (synCid) C) C) (.classMem A D)
      p0001
  have p0003 :=
    @gEqtr4d (synWa (.classMem A D) (.classMem C (synCvv))) (synCfv F A) C
      (synCfv (synCid) C) p0000 p0002
  have p0004 := @gEleq1d (.classEq (.cv x) A) B C (synCvv) hyp_fvmptg_1
  have p0005 := @gDmmpt x D B F hyp_fvmptg_2
  have p0006 :=
    @gElrab2 (.classMem B (synCvv)) (.classMem C (synCvv)) x A D (synCdm F)
      dv_cache_0001 dv_cache_0003 dv_cache_0004 p0004 p0005
  have p0007 :=
    @gBaib (.classMem A (synCdm F)) (.classMem A D) (.classMem C (synCvv)) p0006
  have p0008 :=
    @gNotbid (.classMem A D) (.classMem A (synCdm F)) (.classMem C (synCvv)) p0007
  have p0009 := @gNdmfv A F
  have p0010 :=
    @gSyl6bir (.classMem A D) (.neg (.classMem C (synCvv)))
      (.neg (.classMem A (synCdm F))) (.classEq (synCfv F A) (synC0)) p0008 p0009
  have p0011 :=
    @gImp (.classMem A D) (.neg (.classMem C (synCvv)))
      (.classEq (synCfv F A) (synC0)) p0010
  have p0012 := @gFvprc C (synCid)
  have p0013 :=
    @gAdantl (.neg (.classMem C (synCvv))) (.classEq (synCfv (synCid) C) (synC0))
      (.classMem A D) p0012
  have p0014 :=
    @gEqtr4d (synWa (.classMem A D) (.neg (.classMem C (synCvv)))) (synCfv F A)
      (synC0) (synCfv (synCid) C) p0011 p0013
  have p0015 :=
    @gPm261dan (.classMem A D) (.classMem C (synCvv))
      (.classEq (synCfv F A) (synCfv (synCid) C)) p0003 p0014
  exact p0015

/-- Checked nominal proof certificate identified upstream as `g_fvmpt`. -/
@[expose]
noncomputable def gFvmpt (x : Var) (A : Class) (B : Class) (C : Class) (D : Class)
    (F : Class) (dv_A_x : x ∉ A.fv) (dv_C_x : x ∉ C.fv) (dv_D_x : x ∉ D.fv)
    (hyp_fvmptg_1 : Nominal.NPrf (.imp (.classEq (.cv x) A) (.classEq B C)))
    (hyp_fvmptg_2 : Nominal.NPrf (.classEq F (synCmpt x D B)))
    (hyp_fvmpt_3 : Nominal.NPrf (.classMem C (synCvv))) :
    Nominal.NPrf (.imp (.classMem A D) (.classEq (synCfv F A) C)) :=
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
    @gFvmptg x A B C D (synCvv) F dv_cache_0001 dv_cache_0002 dv_cache_0003 hyp_fvmptg_1
      hyp_fvmptg_2
  have p0001 :=
    @gMpan2 (.classMem A D) (.classMem C (synCvv)) (.classEq (synCfv F A) C)
      hyp_fvmpt_3 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_fvmpts`. -/
@[expose]
noncomputable def gFvmpts (x : Var) (A : Class) (B : Class) (C : Class) (F : Class)
    (V : Class) (dv_C_x : x ∉ C.fv)
    (hyp_fvmpts_1 : Nominal.NPrf (.classEq F (synCmpt x C B))) :
    Nominal.NPrf
      (.imp (synWa (.classMem A C) (.classMem (synCsb A x B) V))
        (.classEq (synCfv F A) (synCsb A x B))) :=
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
  have dv_cache_0006 : y ∉ ((synCsb A x B)).fv :=
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
  have p0000 := @gCsbeq1 x (.cv y) A B
  have p0001 := @gNfcv y B dv_cache_0001
  have p0002 := @gNfcsb1v x (.cv y) B dv_cache_0002
  have p0003 := @gCsbeq1a x (.cv y) B
  have p0004_e02_recanon :
    Nominal.NPrf (.imp (.objEq x y) (.classEq B (synCsb (.cv y) x B))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCsb synWsbc
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0003
  have p0004 :=
    @gCbvmpt x y C B (synCsb (.cv y) x B) dv_cache_0003 dv_cache_0004 p0001 p0002
      p0004_e02_recanon
  have p0005 :=
    @gEqtri F (synCmpt x C B) (synCmpt y C (synCsb (.cv y) x B)) hyp_fvmpts_1 p0004
  have p0006 :=
    @gFvmptg y A (synCsb (.cv y) x B) (synCsb A x B) C V F dv_cache_0005 dv_cache_0006
      dv_cache_0004 p0000 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_fvmptd`. -/
@[expose]
noncomputable def gFvmptd (ph : Wff) (x : Var) (A : Class) (B : Class) (C : Class)
    (D : Class) (F : Class) (V : Class) (dv_A_x : x ∉ A.fv) (dv_C_x : x ∉ C.fv)
    (dv_D_x : x ∉ D.fv) (dv_ph_x : x ∉ ph.fv)
    (hyp_fvmptd_1 : Nominal.NPrf (.imp ph (.classEq F (synCmpt x D B))))
    (hyp_fvmptd_2 : Nominal.NPrf (.imp (synWa ph (.classEq (.cv x) A)) (.classEq B C)))
    (hyp_fvmptd_3 : Nominal.NPrf (.imp ph (.classMem A D)))
    (hyp_fvmptd_4 : Nominal.NPrf (.imp ph (.classMem C V))) :
    Nominal.NPrf (.imp ph (.classEq (synCfv F A) C)) :=
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
  have p0000 := @gFveq1d ph A F (synCmpt x D B) hyp_fvmptd_1
  have p0001 :=
    @gCsbied ph x A B C D dv_cache_0001 dv_cache_0002 dv_cache_0003 hyp_fvmptd_3
      hyp_fvmptd_2
  have p0002 := @gEqeltrd ph (synCsb A x B) C V p0001 hyp_fvmptd_4
  have p0003 := @gEqid (synCmpt x D B)
  have p0004 := @gFvmpts x A B D (synCmpt x D B) V dv_cache_0004 p0003
  have p0005 :=
    @gSyl2anc ph (.classMem A D) (.classMem (synCsb A x B) V)
      (.classEq (synCfv (synCmpt x D B) A) (synCsb A x B)) hyp_fvmptd_3 p0002 p0004
  have p0006 :=
    @gN3eqtrd ph (synCfv F A) (synCfv (synCmpt x D B) A) (synCsb A x B) C p0000
      p0005 p0001
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_fvmpt2i`. -/
@[expose]
noncomputable def gFvmpt2i (x : Var) (A : Class) (B : Class) (F : Class)
    (dv_A_x : x ∉ A.fv) (hyp_fvmpt2_1 : Nominal.NPrf (.classEq F (synCmpt x A B))) :
    Nominal.NPrf
      (.imp (.classMem (.cv x) A) (.classEq (synCfv F (.cv x)) (synCfv (synCid) B))) :=
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
  have p0000 := @gCsbeq1 x (.cv y) (.cv x) B
  have p0001 := @gCsbid x B
  have p0002 :=
    @gSyl6eq (.classEq (.cv y) (.cv x)) (synCsb (.cv y) x B) (synCsb (.cv x) x B) B
      p0000 p0001
  have p0003 := @gNfcv y B dv_cache_0001
  have p0004 := @gNfcsb1v x (.cv y) B dv_cache_0002
  have p0005 := @gCsbeq1a x (.cv y) B
  have p0006_e02_recanon :
    Nominal.NPrf (.imp (.objEq x y) (.classEq B (synCsb (.cv y) x B))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCsb synWsbc
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0005
  have p0006 :=
    @gCbvmpt x y A B (synCsb (.cv y) x B) dv_cache_0003 dv_cache_0004 p0003 p0004
      p0006_e02_recanon
  have p0007 :=
    @gEqtri F (synCmpt x A B) (synCmpt y A (synCsb (.cv y) x B)) hyp_fvmpt2_1 p0006
  have p0008 :=
    @gFvmpti y (.cv x) (synCsb (.cv y) x B) B A F dv_cache_0005 dv_cache_0001
      dv_cache_0004 p0002 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_fvmpt2`. -/
@[expose]
noncomputable def gFvmpt2 (x : Var) (A : Class) (B : Class) (C : Class) (F : Class)
    (dv_A_x : x ∉ A.fv) (hyp_fvmpt2_1 : Nominal.NPrf (.classEq F (synCmpt x A B))) :
    Nominal.NPrf
      (.imp (synWa (.classMem (.cv x) A) (.classMem B C)) (.classEq (synCfv F (.cv x)) B)) :=
  by
  have dv_cache_0001 : x ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have p0000 := @gFvmpt2i x A B F dv_cache_0001 hyp_fvmpt2_1
  have p0001 := @gFvi B C
  have p0002 :=
    @gSylan9eq (.classMem (.cv x) A) (.classMem B C) (synCfv F (.cv x))
      (synCfv (synCid) B) B p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_mpt2mptx`. -/
@[expose]
noncomputable def gMpt2mptx (x : Var) (y : Var) (z : Var) (A : Class) (B : Class)
    (C : Class) (D : Class) (_dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv)
    (dv_B_y : y ∉ B.fv) (dv_B_z : z ∉ B.fv) (dv_C_x : x ∉ C.fv) (dv_C_y : y ∉ C.fv)
    (dv_D_z : z ∉ D.fv) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z)
    (hyp_mpt2mpt_1 :
      Nominal.NPrf (.imp (.classEq (.cv z) (synCop (.cv x) (.cv y))) (.classEq C D))) :
    Nominal.NPrf
      (.classEq (synCmpt z (synCiun x A (synCxp (synCsn (.cv x)) B)) C)
        (synCmpt2 x A y B D)) :=
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
  have dv_cache_0001 : w ∉ ((synCiun x A (synCxp (synCsn (.cv x)) B))).fv := by
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
      ((synWa (synWa (.classMem (.cv x) A) (.classMem (.cv y) B)) (.classEq (.cv w) D))).fv :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfMpt z w
      (synCiun x A (synCxp (synCsn (.cv x)) B)) C dv_cache_0001 dv_cache_0002
      dv_cache_0003
  have p0001 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfMpt2 x y w A B D
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
  have p0002 :=
    @gEliunxp x y A B (.cv z) dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
      dv_cache_0013
  have p0003 :=
    @gAnbi1i (.classMem (.cv z) (synCiun x A (synCxp (synCsn (.cv x)) B)))
      (synWex x (synWex y (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y)))
            (synWa (.classMem (.cv x) A) (.classMem (.cv y) B)))))
      (.classEq (.cv w) C) p0002
  have p0004 :=
    @gN1941vv
      (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y)))
        (synWa (.classMem (.cv x) A) (.classMem (.cv y) B)))
      (.classEq (.cv w) C) x y dv_cache_0014 dv_cache_0015
  have p0005 :=
    @gAnass (.classEq (.cv z) (synCop (.cv x) (.cv y)))
      (synWa (.classMem (.cv x) A) (.classMem (.cv y) B)) (.classEq (.cv w) C)
  have p0006 :=
    @gEqeq2d (.classEq (.cv z) (synCop (.cv x) (.cv y))) C D (.cv w) hyp_mpt2mpt_1
  have p0007 :=
    @gAnbi2d (.classEq (.cv z) (synCop (.cv x) (.cv y))) (.classEq (.cv w) C)
      (.classEq (.cv w) D) (synWa (.classMem (.cv x) A) (.classMem (.cv y) B)) p0006
  have p0008 :=
    @gPm532i (.classEq (.cv z) (synCop (.cv x) (.cv y)))
      (synWa (synWa (.classMem (.cv x) A) (.classMem (.cv y) B)) (.classEq (.cv w) C))
      (synWa (synWa (.classMem (.cv x) A) (.classMem (.cv y) B)) (.classEq (.cv w) D))
      p0007
  have p0009 :=
    @gBitri
      (synWa (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y)))
          (synWa (.classMem (.cv x) A) (.classMem (.cv y) B))) (.classEq (.cv w) C))
      (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y)))
        (synWa (synWa (.classMem (.cv x) A) (.classMem (.cv y) B)) (.classEq (.cv w) C)))
      (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y)))
        (synWa (synWa (.classMem (.cv x) A) (.classMem (.cv y) B)) (.classEq (.cv w) D)))
      p0005 p0008
  have p0010 :=
    @gN2exbii
      (synWa (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y)))
          (synWa (.classMem (.cv x) A) (.classMem (.cv y) B))) (.classEq (.cv w) C))
      (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y)))
        (synWa (synWa (.classMem (.cv x) A) (.classMem (.cv y) B)) (.classEq (.cv w) D)))
      x y p0009
  have p0011 :=
    @gN3bitr2i
      (synWa (.classMem (.cv z) (synCiun x A (synCxp (synCsn (.cv x)) B)))
        (.classEq (.cv w) C))
      (synWa (synWex x (synWex y (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y)))
              (synWa (.classMem (.cv x) A) (.classMem (.cv y) B))))) (.classEq (.cv w) C))
      (synWex x (synWex y (synWa (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y)))
              (synWa (.classMem (.cv x) A) (.classMem (.cv y) B))) (.classEq (.cv w) C))))
      (synWex x (synWex y (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y)))
            (synWa (synWa (.classMem (.cv x) A) (.classMem (.cv y) B))
              (.classEq (.cv w) D)))))
      p0003 p0004 p0010
  have p0012 :=
    @gOpabbii
      (synWa (.classMem (.cv z) (synCiun x A (synCxp (synCsn (.cv x)) B)))
        (.classEq (.cv w) C))
      (synWex x (synWex y (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y)))
            (synWa (synWa (.classMem (.cv x) A) (.classMem (.cv y) B))
              (.classEq (.cv w) D)))))
      z w p0011
  have p0013 :=
    @gDfoprab2
      (synWa (synWa (.classMem (.cv x) A) (.classMem (.cv y) B)) (.classEq (.cv w) D)) x
      y w z dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0003 dv_cache_0007
      dv_cache_0008
  have p0014 :=
    @gEqtr4i
      (synCopab z w (synWa (.classMem (.cv z) (synCiun x A (synCxp (synCsn (.cv x)) B)))
          (.classEq (.cv w) C)))
      (synCopab z w (synWex x (synWex y (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y)))
              (synWa (synWa (.classMem (.cv x) A) (.classMem (.cv y) B))
                (.classEq (.cv w) D))))))
      (synCoprab x y w (synWa (synWa (.classMem (.cv x) A) (.classMem (.cv y) B))
          (.classEq (.cv w) D)))
      p0012 p0013
  have p0015 :=
    @gEqtr4i (synCmpt2 x A y B D)
      (synCoprab x y w (synWa (synWa (.classMem (.cv x) A) (.classMem (.cv y) B))
          (.classEq (.cv w) D)))
      (synCopab z w (synWa (.classMem (.cv z) (synCiun x A (synCxp (synCsn (.cv x)) B)))
          (.classEq (.cv w) C)))
      p0001 p0014
  have p0016 :=
    @gEqtr4i (synCmpt z (synCiun x A (synCxp (synCsn (.cv x)) B)) C)
      (synCopab z w (synWa (.classMem (.cv z) (synCiun x A (synCxp (synCsn (.cv x)) B)))
          (.classEq (.cv w) C)))
      (synCmpt2 x A y B D) p0000 p0015
  exact p0016

/-- Checked nominal proof certificate identified upstream as `g_ovmpt2ga`. -/
@[expose]
noncomputable def gOvmpt2ga (x : Var) (y : Var) (A : Class) (B : Class) (C : Class)
    (D : Class) (R : Class) (S : Class) (F : Class) (H : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_C_x : x ∉ C.fv)
    (dv_C_y : y ∉ C.fv) (dv_D_x : x ∉ D.fv) (dv_D_y : y ∉ D.fv) (dv_S_x : x ∉ S.fv)
    (dv_S_y : y ∉ S.fv) (dv_x_y : x ≠ y)
    (hyp_ovmpt2ga_1 : Nominal.NPrf
        (.imp (synWa (.classEq (.cv x) A) (.classEq (.cv y) B)) (.classEq R S)))
    (hyp_ovmpt2ga_2 : Nominal.NPrf (.classEq F (synCmpt2 x C y D R))) :
    Nominal.NPrf
      (.imp (synW3a (.classMem A C) (.classMem B D) (.classMem S H))
        (.classEq (synCo A F B) S)) :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfMpt2 x y z C D R
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0001 :=
    @gEqtri F (synCmpt2 x C y D R)
      (synCoprab x y z (synWa (synWa (.classMem (.cv x) C) (.classMem (.cv y) D))
          (.classEq (.cv z) R)))
      hyp_ovmpt2ga_2 p0000
  have p0002 :=
    @gOv2ag x y z A B C D R S F H dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
      dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0001 dv_cache_0014
      dv_cache_0015 dv_cache_0002 dv_cache_0003 dv_cache_0016 dv_cache_0017 dv_cache_0018
      dv_cache_0019 dv_cache_0004 dv_cache_0005 hyp_ovmpt2ga_1 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_ovmpt2g`. -/
@[expose]
noncomputable def gOvmpt2g (x : Var) (y : Var) (A : Class) (B : Class) (C : Class)
    (D : Class) (R : Class) (S : Class) (F : Class) (G : Class) (H : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv)
    (dv_C_x : x ∉ C.fv) (dv_C_y : y ∉ C.fv) (dv_D_x : x ∉ D.fv) (dv_D_y : y ∉ D.fv)
    (_dv_G_x : x ∉ G.fv) (dv_S_x : x ∉ S.fv) (dv_S_y : y ∉ S.fv) (dv_x_y : x ≠ y)
    (hyp_ovmpt2g_1 : Nominal.NPrf (.imp (.classEq (.cv x) A) (.classEq R G)))
    (hyp_ovmpt2g_2 : Nominal.NPrf (.imp (.classEq (.cv y) B) (.classEq G S)))
    (hyp_ovmpt2g_3 : Nominal.NPrf (.classEq F (synCmpt2 x C y D R))) :
    Nominal.NPrf
      (.imp (synW3a (.classMem A C) (.classMem B D) (.classMem S H))
        (.classEq (synCo A F B) S)) :=
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
    @gSylan9eq (.classEq (.cv x) A) (.classEq (.cv y) B) R G S hyp_ovmpt2g_1
      hyp_ovmpt2g_2
  have p0001 :=
    @gOvmpt2ga x y A B C D R S F H dv_cache_0001 dv_cache_0002 dv_cache_0003
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

/-- Checked nominal proof certificate identified upstream as `g_ovmpt2`. -/
@[expose]
noncomputable def gOvmpt2 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class)
    (D : Class) (R : Class) (S : Class) (F : Class) (G : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_C_x : x ∉ C.fv)
    (dv_C_y : y ∉ C.fv) (dv_D_x : x ∉ D.fv) (dv_D_y : y ∉ D.fv) (dv_G_x : x ∉ G.fv)
    (dv_S_x : x ∉ S.fv) (dv_S_y : y ∉ S.fv) (dv_x_y : x ≠ y)
    (hyp_ovmpt2g_1 : Nominal.NPrf (.imp (.classEq (.cv x) A) (.classEq R G)))
    (hyp_ovmpt2g_2 : Nominal.NPrf (.imp (.classEq (.cv y) B) (.classEq G S)))
    (hyp_ovmpt2g_3 : Nominal.NPrf (.classEq F (synCmpt2 x C y D R)))
    (hyp_ovmpt2_4 : Nominal.NPrf (.classMem S (synCvv))) :
    Nominal.NPrf
      (.imp (synWa (.classMem A C) (.classMem B D)) (.classEq (synCo A F B) S)) :=
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
    @gOvmpt2g x y A B C D R S F G (synCvv) dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
      dv_cache_0010 dv_cache_0011 dv_cache_0012 hyp_ovmpt2g_1 hyp_ovmpt2g_2 hyp_ovmpt2g_3
  have p0001 :=
    @gMp3an3 (.classMem A C) (.classMem B D) (.classMem S (synCvv))
      (.classEq (synCo A F B) S) hyp_ovmpt2_4 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_mptv`. -/
@[expose]
noncomputable def gMptv (x : Var) (y : Var) (B : Class) (dv_B_y : y ∉ B.fv)
    (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.classEq (synCmpt x (synCvv) B) (synCopab x y (.classEq (.cv y) B))) :=
  by
  have dv_cache_0001 : y ∉ ((synCvv)).fv := by
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfMpt x y (synCvv) B
      dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 := @gVex x
  have p0002 := @gBiantrur (.classMem (.cv x) (synCvv)) (.classEq (.cv y) B) p0001
  have p0003 :=
    @gOpabbii (.classEq (.cv y) B)
      (synWa (.classMem (.cv x) (synCvv)) (.classEq (.cv y) B)) x y p0002
  have p0004 :=
    @gEqtr4i (synCmpt x (synCvv) B)
      (synCopab x y (synWa (.classMem (.cv x) (synCvv)) (.classEq (.cv y) B)))
      (synCopab x y (.classEq (.cv y) B)) p0000 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_f1od`. -/
@[expose]
noncomputable def gF1od (ph : Wff) (x : Var) (y : Var) (A : Class) (B : Class)
    (C : Class) (D : Class) (F : Class) (W : Class) (X : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_C_y : y ∉ C.fv)
    (dv_D_x : x ∉ D.fv) (dv_ph_x : x ∉ ph.fv) (dv_ph_y : y ∉ ph.fv) (dv_x_y : x ≠ y)
    (hyp_f1od_1 : Nominal.NPrf (.classEq F (synCmpt x A C)))
    (hyp_f1od_2 : Nominal.NPrf (.imp (synWa ph (.classMem (.cv x) A)) (.classMem C W)))
    (hyp_f1od_3 : Nominal.NPrf (.imp (synWa ph (.classMem (.cv y) B)) (.classMem D X)))
    (hyp_f1od_4 : Nominal.NPrf (.imp ph
          (synWb (synWa (.classMem (.cv x) A) (.classEq (.cv y) C))
            (synWa (.classMem (.cv y) B) (.classEq (.cv x) D))))) :
    Nominal.NPrf (.imp ph (synWf1o F A B)) :=
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
  have p0000 := @gRalrimiva ph (.classMem C W) x A dv_cache_0001 hyp_f1od_2
  have p0001 := @gFnmpt x A C F W dv_cache_0002 hyp_f1od_1
  have p0002 := @gSyl ph (synWral x A (.classMem C W)) (synWfn F A) p0000 p0001
  have p0003 := @gRalrimiva ph (.classMem D X) y B dv_cache_0003 hyp_f1od_3
  have p0004 := @gEqid (synCmpt y B D)
  have p0005 := @gFnmpt y B D (synCmpt y B D) X dv_cache_0004 p0004
  have p0006 :=
    @gSyl ph (synWral y B (.classMem D X)) (synWfn (synCmpt y B D) B) p0003 p0005
  have p0007 :=
    @gOpabbidv ph (synWa (.classMem (.cv x) A) (.classEq (.cv y) C))
      (synWa (.classMem (.cv y) B) (.classEq (.cv x) D)) y x dv_cache_0003 dv_cache_0001
      hyp_f1od_4
  have p0008 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfMpt x y A C
      dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0009 :=
    @gEqtri F (synCmpt x A C)
      (synCopab x y (synWa (.classMem (.cv x) A) (.classEq (.cv y) C))) hyp_f1od_1 p0008
  have p0010 :=
    @gCnveqi F (synCopab x y (synWa (.classMem (.cv x) A) (.classEq (.cv y) C))) p0009
  have p0011 :=
    @gCnvopab (synWa (.classMem (.cv x) A) (.classEq (.cv y) C)) x y dv_cache_0007
  have p0012 :=
    @gEqtri (synCcnv F)
      (synCcnv (synCopab x y (synWa (.classMem (.cv x) A) (.classEq (.cv y) C))))
      (synCopab y x (synWa (.classMem (.cv x) A) (.classEq (.cv y) C))) p0010 p0011
  have p0013 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfMpt y x B D
      dv_cache_0008 dv_cache_0009 dv_cache_0010
  have p0014 :=
    @gN3eqtr4g ph (synCopab y x (synWa (.classMem (.cv x) A) (.classEq (.cv y) C)))
      (synCopab y x (synWa (.classMem (.cv y) B) (.classEq (.cv x) D))) (synCcnv F)
      (synCmpt y B D) p0007 p0012 p0013
  have p0015 := @gFneq1d ph B (synCcnv F) (synCmpt y B D) p0014
  have p0016 :=
    @gMpbird ph (synWfn (synCcnv F) B) (synWfn (synCmpt y B D) B) p0006 p0015
  have p0017 := @gDff1o4 A B F
  have p0018 :=
    @gSylanbrc ph (synWfn F A) (synWfn (synCcnv F) B) (synWf1o F A B) p0002 p0016
      p0017
  exact p0018

/-- Checked nominal proof certificate identified upstream as `g_f1o2d`. -/
@[expose]
noncomputable def gF1o2d (ph : Wff) (x : Var) (y : Var) (A : Class) (B : Class)
    (C : Class) (D : Class) (F : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv)
    (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_C_y : y ∉ C.fv) (dv_D_x : x ∉ D.fv)
    (dv_ph_x : x ∉ ph.fv) (dv_ph_y : y ∉ ph.fv) (dv_x_y : x ≠ y)
    (hyp_f1od_1 : Nominal.NPrf (.classEq F (synCmpt x A C)))
    (hyp_f1o2d_2 : Nominal.NPrf (.imp (synWa ph (.classMem (.cv x) A)) (.classMem C B)))
    (hyp_f1o2d_3 : Nominal.NPrf (.imp (synWa ph (.classMem (.cv y) B)) (.classMem D A)))
    (hyp_f1o2d_4 : Nominal.NPrf
        (.imp (synWa ph (synWa (.classMem (.cv x) A) (.classMem (.cv y) B)))
          (synWb (.classEq (.cv x) D) (.classEq (.cv y) C)))) :
    Nominal.NPrf (.imp ph (synWf1o F A B)) :=
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
  have p0000 := @gEleq1a C B (.cv y)
  have p0001 :=
    @gSyl (synWa ph (.classMem (.cv x) A)) (.classMem C B)
      (.imp (.classEq (.cv y) C) (.classMem (.cv y) B)) hyp_f1o2d_2 p0000
  have p0002 :=
    @gImpr ph (.classMem (.cv x) A) (.classEq (.cv y) C) (.classMem (.cv y) B) p0001
  have p0003 :=
    @gBiimpar (synWa ph (synWa (.classMem (.cv x) A) (.classMem (.cv y) B)))
      (.classEq (.cv x) D) (.classEq (.cv y) C) hyp_f1o2d_4
  have p0004 :=
    @gExp42 ph (.classMem (.cv x) A) (.classMem (.cv y) B) (.classEq (.cv y) C)
      (.classEq (.cv x) D) p0003
  have p0005 :=
    @gCom34 ph (.classMem (.cv x) A) (.classMem (.cv y) B) (.classEq (.cv y) C)
      (.classEq (.cv x) D) p0004
  have p0006 :=
    @gImp32 ph (.classMem (.cv x) A) (.classEq (.cv y) C)
      (.imp (.classMem (.cv y) B) (.classEq (.cv x) D)) p0005
  have p0007 :=
    @gJcai (synWa ph (synWa (.classMem (.cv x) A) (.classEq (.cv y) C)))
      (.classMem (.cv y) B) (.classEq (.cv x) D) p0002 p0006
  have p0008 := @gEleq1a D A (.cv x)
  have p0009 :=
    @gSyl (synWa ph (.classMem (.cv y) B)) (.classMem D A)
      (.imp (.classEq (.cv x) D) (.classMem (.cv x) A)) hyp_f1o2d_3 p0008
  have p0010 :=
    @gImpr ph (.classMem (.cv y) B) (.classEq (.cv x) D) (.classMem (.cv x) A) p0009
  have p0011 :=
    @gBiimpa (synWa ph (synWa (.classMem (.cv x) A) (.classMem (.cv y) B)))
      (.classEq (.cv x) D) (.classEq (.cv y) C) hyp_f1o2d_4
  have p0012 :=
    @gExp42 ph (.classMem (.cv x) A) (.classMem (.cv y) B) (.classEq (.cv x) D)
      (.classEq (.cv y) C) p0011
  have p0013 :=
    @gCom23 ph (.classMem (.cv x) A) (.classMem (.cv y) B)
      (.imp (.classEq (.cv x) D) (.classEq (.cv y) C)) p0012
  have p0014 :=
    @gCom34 ph (.classMem (.cv y) B) (.classMem (.cv x) A) (.classEq (.cv x) D)
      (.classEq (.cv y) C) p0013
  have p0015 :=
    @gImp32 ph (.classMem (.cv y) B) (.classEq (.cv x) D)
      (.imp (.classMem (.cv x) A) (.classEq (.cv y) C)) p0014
  have p0016 :=
    @gJcai (synWa ph (synWa (.classMem (.cv y) B) (.classEq (.cv x) D)))
      (.classMem (.cv x) A) (.classEq (.cv y) C) p0010 p0015
  have p0017 :=
    @gImpbida ph (synWa (.classMem (.cv x) A) (.classEq (.cv y) C))
      (synWa (.classMem (.cv y) B) (.classEq (.cv x) D)) p0007 p0016
  have p0018 :=
    @gF1od ph x y A B C D F B A dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
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

/-- Checked nominal proof certificate identified upstream as `g_fmpt2x`. -/
@[expose]
noncomputable def gFmpt2x (x : Var) (y : Var) (A : Class) (B : Class) (C : Class)
    (D : Class) (F : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_y : y ∉ B.fv)
    (dv_D_x : x ∉ D.fv) (dv_D_y : y ∉ D.fv) (dv_x_y : x ≠ y)
    (hyp_fmpt2x_1 : Nominal.NPrf (.classEq F (synCmpt2 x A y B C))) :
    Nominal.NPrf
      (synWb (synWral x A (synWral y B (.classMem C D)))
        (synWf F (synCiun x A (synCxp (synCsn (.cv x)) B)) D)) :=
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
  have dv_cache_0001 : x ∉ ((Wff.classEq (.cv v) (synCop (.cv z) (.cv w)))).fv := by
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
  have dv_cache_0005 : v ∉ ((synCsb (.cv z) x B)).fv :=
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
  have dv_cache_0006 : w ∉ ((synCsb (.cv z) x B)).fv :=
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
      ((Wff.classMem (synCsb (synCfv (synC1st) (.cv v)) x
            (synCsb (synCfv (synC2nd) (.cv v)) y C)) D)).fv :=
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
      ((Wff.classMem (synCsb (synCfv (synC1st) (.cv v)) x
            (synCsb (synCfv (synC2nd) (.cv v)) y C)) D)).fv :=
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
    v ∉ ((Wff.classMem (synCsb (.cv z) x (synCsb (.cv w) y C)) D)).fv :=
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
      ((synWa (synWa (.classMem (.cv x) A) (.classMem (.cv y) B)) (.classEq (.cv v) C))).fv :=
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
      ((synWa (synWa (.classMem (.cv x) A) (.classMem (.cv y) B)) (.classEq (.cv v) C))).fv :=
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
    y ∉ ((synWa (.classMem (.cv z) A) (.classMem (.cv w) (synCsb (.cv z) x B)))).fv :=
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
  have dv_cache_0035 : v ∉ ((synCsb (.cv z) x (synCsb (.cv w) y C))).fv :=
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
      ((synCsb (synCfv (synC1st) (.cv v)) x
          (synCsb (synCfv (synC2nd) (.cv v)) y C))).fv :=
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
      ((synCsb (synCfv (synC1st) (.cv v)) x
          (synCsb (synCfv (synC2nd) (.cv v)) y C))).fv :=
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
    v ∉ ((synCiun z A (synCxp (synCsn (.cv z)) (synCsb (.cv z) x B)))).fv :=
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
  have dv_cache_0040 : z ∉ ((synWral y B (.classMem C D))).fv :=
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
  have dv_cache_0048 : z ∉ ((synCxp (synCsn (.cv x)) B)).fv :=
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
  have dv_cache_0049 : x ∉ ((synCsn (.cv z))).fv :=
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
  have p0000 := @gVex z
  have p0001 := @gVex w
  have p0002 := @gOp1std (.cv z) (.cv w) (.cv v) p0000 p0001
  have p0003 :=
    @gCsbeq1d (.classEq (.cv v) (synCop (.cv z) (.cv w))) x (synCfv (synC1st) (.cv v))
      (.cv z) (synCsb (synCfv (synC2nd) (.cv v)) y C) p0002
  have p0004 := @gOp2ndd (.cv z) (.cv w) (.cv v) p0000 p0001
  have p0005 :=
    @gCsbeq1d (.classEq (.cv v) (synCop (.cv z) (.cv w))) y (synCfv (synC2nd) (.cv v))
      (.cv w) C p0004
  have p0006 :=
    @gCsbeq2dv (.classEq (.cv v) (synCop (.cv z) (.cv w))) x (.cv z)
      (synCsb (synCfv (synC2nd) (.cv v)) y C) (synCsb (.cv w) y C) dv_cache_0001 p0005
  have p0007 :=
    @gEqtrd (.classEq (.cv v) (synCop (.cv z) (.cv w)))
      (synCsb (synCfv (synC1st) (.cv v)) x (synCsb (synCfv (synC2nd) (.cv v)) y C))
      (synCsb (.cv z) x (synCsb (synCfv (synC2nd) (.cv v)) y C))
      (synCsb (.cv z) x (synCsb (.cv w) y C)) p0003 p0006
  have p0008 :=
    @gEleq1d (.classEq (.cv v) (synCop (.cv z) (.cv w)))
      (synCsb (synCfv (synC1st) (.cv v)) x (synCsb (synCfv (synC2nd) (.cv v)) y C))
      (synCsb (.cv z) x (synCsb (.cv w) y C)) D p0007
  have p0009 :=
    @gRaliunxp
      (.classMem (synCsb (synCfv (synC1st) (.cv v)) x
          (synCsb (synCfv (synC2nd) (.cv v)) y C)) D)
      (.classMem (synCsb (.cv z) x (synCsb (.cv w) y C)) D) v z w A
      (synCsb (.cv z) x B) dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 p0008
  have p0010 :=
    @gNfv
      (synWa (synWa (.classMem (.cv x) A) (.classMem (.cv y) B)) (.classEq (.cv v) C)) z
      dv_cache_0013
  have p0011 :=
    @gNfv
      (synWa (synWa (.classMem (.cv x) A) (.classMem (.cv y) B)) (.classEq (.cv v) C)) w
      dv_cache_0014
  have p0012 := @gNfv (.classMem (.cv z) A) x dv_cache_0015
  have p0013 := @gNfcsb1v x (.cv z) B dv_cache_0016
  have p0014 := @gNfcri x w (synCsb (.cv z) x B) dv_cache_0017 p0013
  have p0015 :=
    @gNfan (.classMem (.cv z) A) (.classMem (.cv w) (synCsb (.cv z) x B)) x p0012 p0014
  have p0016 := @gNfcsb1v x (.cv z) (synCsb (.cv w) y C) dv_cache_0016
  have p0017 :=
    @gNfeq2 x (.cv v) (synCsb (.cv z) x (synCsb (.cv w) y C)) dv_cache_0018 p0016
  have p0018 :=
    @gNfan (synWa (.classMem (.cv z) A) (.classMem (.cv w) (synCsb (.cv z) x B)))
      (.classEq (.cv v) (synCsb (.cv z) x (synCsb (.cv w) y C))) x p0015 p0017
  have p0019 :=
    @gNfv (synWa (.classMem (.cv z) A) (.classMem (.cv w) (synCsb (.cv z) x B))) y
      dv_cache_0019
  have p0020 := @gNfcv y (.cv z) dv_cache_0020
  have p0021 := @gNfcsb1v y (.cv w) C dv_cache_0021
  have p0022 := @gNfcsb y x (.cv z) (synCsb (.cv w) y C) p0020 p0021
  have p0023 :=
    @gNfeq2 y (.cv v) (synCsb (.cv z) x (synCsb (.cv w) y C)) dv_cache_0022 p0022
  have p0024 :=
    @gNfan (synWa (.classMem (.cv z) A) (.classMem (.cv w) (synCsb (.cv z) x B)))
      (.classEq (.cv v) (synCsb (.cv z) x (synCsb (.cv w) y C))) y p0019 p0023
  have p0025 := @gEleq1 (.cv x) (.cv z) A
  have p0026 :=
    @gAdantr (.classEq (.cv x) (.cv z))
      (synWb (.classMem (.cv x) A) (.classMem (.cv z) A)) (.classEq (.cv y) (.cv w))
      p0025
  have p0027 := @gEleq1 (.cv y) (.cv w) B
  have p0028 := @gCsbeq1a x (.cv z) B
  have p0029 := @gEleq2d (.classEq (.cv x) (.cv z)) B (synCsb (.cv z) x B) (.cv w) p0028
  have p0030 :=
    @gSylan9bbr (.classEq (.cv y) (.cv w)) (.classMem (.cv y) B) (.classMem (.cv w) B)
      (.classEq (.cv x) (.cv z)) (.classMem (.cv w) (synCsb (.cv z) x B)) p0027 p0029
  have p0031 :=
    @gAnbi12d (synWa (.classEq (.cv x) (.cv z)) (.classEq (.cv y) (.cv w)))
      (.classMem (.cv x) A) (.classMem (.cv z) A) (.classMem (.cv y) B)
      (.classMem (.cv w) (synCsb (.cv z) x B)) p0026 p0030
  have p0032 := @gCsbeq1a y (.cv w) C
  have p0033 := @gCsbeq1a x (.cv z) (synCsb (.cv w) y C)
  have p0034 :=
    @gSylan9eqr (.classEq (.cv y) (.cv w)) (.classEq (.cv x) (.cv z)) C
      (synCsb (.cv w) y C) (synCsb (.cv z) x (synCsb (.cv w) y C)) p0032 p0033
  have p0035 :=
    @gEqeq2d (synWa (.classEq (.cv x) (.cv z)) (.classEq (.cv y) (.cv w))) C
      (synCsb (.cv z) x (synCsb (.cv w) y C)) (.cv v) p0034
  have p0036 :=
    @gAnbi12d (synWa (.classEq (.cv x) (.cv z)) (.classEq (.cv y) (.cv w)))
      (synWa (.classMem (.cv x) A) (.classMem (.cv y) B))
      (synWa (.classMem (.cv z) A) (.classMem (.cv w) (synCsb (.cv z) x B)))
      (.classEq (.cv v) C) (.classEq (.cv v) (synCsb (.cv z) x (synCsb (.cv w) y C)))
      p0031 p0035
  have p0037_e04_recanon :
    Nominal.NPrf
      (.imp (synWa (.objEq x z) (.objEq y w)) (synWb
          (synWa (synWa (.classMem (.cv x) A) (.classMem (.cv y) B)) (.classEq (.cv v) C))
          (synWa (synWa (.classMem (.cv z) A) (.classMem (.cv w) (synCsb (.cv z) x B)))
            (.classEq (.cv v) (synCsb (.cv z) x (synCsb (.cv w) y C)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWa synWb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0036
  have p0037 :=
    @gCbvoprab12
      (synWa (synWa (.classMem (.cv x) A) (.classMem (.cv y) B)) (.classEq (.cv v) C))
      (synWa (synWa (.classMem (.cv z) A) (.classMem (.cv w) (synCsb (.cv z) x B)))
        (.classEq (.cv v) (synCsb (.cv z) x (synCsb (.cv w) y C))))
      x y v z w dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
      dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 p0010 p0011
      p0018 p0024 p0037_e04_recanon
  have p0038 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfMpt2 x y v A B C
      dv_cache_0002 dv_cache_0033 dv_cache_0034 dv_cache_0031 dv_cache_0032
  have p0039 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfMpt2 z w v A
      (synCsb (.cv z) x B) (synCsb (.cv z) x (synCsb (.cv w) y C)) dv_cache_0002
      dv_cache_0005 dv_cache_0035 dv_cache_0029 dv_cache_0026
  have p0040 :=
    @gN3eqtr4i
      (synCoprab x y v (synWa (synWa (.classMem (.cv x) A) (.classMem (.cv y) B))
          (.classEq (.cv v) C)))
      (synCoprab z w v
        (synWa (synWa (.classMem (.cv z) A) (.classMem (.cv w) (synCsb (.cv z) x B)))
          (.classEq (.cv v) (synCsb (.cv z) x (synCsb (.cv w) y C)))))
      (synCmpt2 x A y B C)
      (synCmpt2 z A w (synCsb (.cv z) x B) (synCsb (.cv z) x (synCsb (.cv w) y C)))
      p0037 p0038 p0039
  have p0041 :=
    @gMpt2mptx z w v A (synCsb (.cv z) x B)
      (synCsb (synCfv (synC1st) (.cv v)) x (synCsb (synCfv (synC2nd) (.cv v)) y C))
      (synCsb (.cv z) x (synCsb (.cv w) y C)) dv_cache_0003 dv_cache_0004 dv_cache_0002
      dv_cache_0006 dv_cache_0005 dv_cache_0036 dv_cache_0037 dv_cache_0035 dv_cache_0012
      dv_cache_0029 dv_cache_0026 p0007
  have p0042 :=
    @gN3eqtr4i (synCmpt2 x A y B C)
      (synCmpt2 z A w (synCsb (.cv z) x B) (synCsb (.cv z) x (synCsb (.cv w) y C))) F
      (synCmpt v (synCiun z A (synCxp (synCsn (.cv z)) (synCsb (.cv z) x B)))
        (synCsb (synCfv (synC1st) (.cv v)) x (synCsb (synCfv (synC2nd) (.cv v)) y C)))
      p0040 hyp_fmpt2x_1 p0041
  have p0043 :=
    @gFmpt v (synCiun z A (synCxp (synCsn (.cv z)) (synCsb (.cv z) x B))) D
      (synCsb (synCfv (synC1st) (.cv v)) x (synCsb (synCfv (synC2nd) (.cv v)) y C))
      F dv_cache_0038 dv_cache_0039 p0042
  have p0044 :=
    @gBitr3i
      (synWral z A (synWral w (synCsb (.cv z) x B)
          (.classMem (synCsb (.cv z) x (synCsb (.cv w) y C)) D)))
      (synWral v (synCiun z A (synCxp (synCsn (.cv z)) (synCsb (.cv z) x B))) (.classMem
          (synCsb (synCfv (synC1st) (.cv v)) x (synCsb (synCfv (synC2nd) (.cv v)) y C))
          D))
      (synWf F (synCiun z A (synCxp (synCsn (.cv z)) (synCsb (.cv z) x B))) D) p0009
      p0043
  have p0045 := @gNfv (synWral y B (.classMem C D)) z dv_cache_0040
  have p0046 := @gNfel1 x (synCsb (.cv z) x (synCsb (.cv w) y C)) D dv_cache_0041 p0016
  have p0047 :=
    @gNfral (.classMem (synCsb (.cv z) x (synCsb (.cv w) y C)) D) x w
      (synCsb (.cv z) x B) p0013 p0046
  have p0048 := @gNfv (.classMem C D) w dv_cache_0042
  have p0049 := @gNfel1 y (synCsb (.cv w) y C) D dv_cache_0043 p0021
  have p0050 := @gEleq1d (.classEq (.cv y) (.cv w)) C (synCsb (.cv w) y C) D p0032
  have p0051_e02_recanon :
    Nominal.NPrf
      (.imp (.objEq y w) (synWb (.classMem C D) (.classMem (synCsb (.cv w) y C) D))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCsb synWsbc
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0050
  have p0051 :=
    @gCbvral (.classMem C D) (.classMem (synCsb (.cv w) y C) D) y w B dv_cache_0044
      dv_cache_0045 p0048 p0049 p0051_e02_recanon
  have p0052 :=
    @gEleq1d (.classEq (.cv x) (.cv z)) (synCsb (.cv w) y C)
      (synCsb (.cv z) x (synCsb (.cv w) y C)) D p0033
  have p0053 :=
    @gRaleqbidv (.classEq (.cv x) (.cv z)) (.classMem (synCsb (.cv w) y C) D)
      (.classMem (synCsb (.cv z) x (synCsb (.cv w) y C)) D) w B (synCsb (.cv z) x B)
      dv_cache_0045 dv_cache_0006 dv_cache_0046 p0028 p0052
  have p0054 :=
    @gSyl5bb (synWral y B (.classMem C D))
      (synWral w B (.classMem (synCsb (.cv w) y C) D)) (.classEq (.cv x) (.cv z))
      (synWral w (synCsb (.cv z) x B) (.classMem (synCsb (.cv z) x (synCsb (.cv w) y C)) D))
      p0051 p0053
  have p0055_e02_recanon :
    Nominal.NPrf
      (.imp (.objEq x z) (synWb (synWral y B (.classMem C D))
          (synWral w (synCsb (.cv z) x B)
            (.classMem (synCsb (.cv z) x (synCsb (.cv w) y C)) D)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWral
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0054
  have p0055 :=
    @gCbvral (synWral y B (.classMem C D))
      (synWral w (synCsb (.cv z) x B) (.classMem (synCsb (.cv z) x (synCsb (.cv w) y C)) D))
      x z A dv_cache_0047 dv_cache_0003 p0045 p0047 p0055_e02_recanon
  have p0056 := @gNfcv z (synCxp (synCsn (.cv x)) B) dv_cache_0048
  have p0057 := @gNfcv x (synCsn (.cv z)) dv_cache_0049
  have p0058 := @gNfxp x (synCsn (.cv z)) (synCsb (.cv z) x B) p0057 p0013
  have p0059 := @gSneq (.cv x) (.cv z)
  have p0060 :=
    @gXpeq12d (.classEq (.cv x) (.cv z)) (synCsn (.cv x)) (synCsn (.cv z)) B
      (synCsb (.cv z) x B) p0059 p0028
  have p0061_e02_recanon :
    Nominal.NPrf
      (.imp (.objEq x z) (.classEq (synCxp (synCsn (.cv x)) B)
          (synCxp (synCsn (.cv z)) (synCsb (.cv z) x B)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCxp synCopab synWex synWa synCsn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csb]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0060
  have p0061 :=
    @gCbviun x z A (synCxp (synCsn (.cv x)) B)
      (synCxp (synCsn (.cv z)) (synCsb (.cv z) x B)) dv_cache_0047 dv_cache_0003 p0056
      p0058 p0061_e02_recanon
  have p0062 :=
    @gFeq2i (synCiun x A (synCxp (synCsn (.cv x)) B))
      (synCiun z A (synCxp (synCsn (.cv z)) (synCsb (.cv z) x B))) D F p0061
  have p0063 :=
    @gN3bitr4i
      (synWral z A (synWral w (synCsb (.cv z) x B)
          (.classMem (synCsb (.cv z) x (synCsb (.cv w) y C)) D)))
      (synWf F (synCiun z A (synCxp (synCsn (.cv z)) (synCsb (.cv z) x B))) D)
      (synWral x A (synWral y B (.classMem C D)))
      (synWf F (synCiun x A (synCxp (synCsn (.cv x)) B)) D) p0044 p0055 p0062
  exact p0063

/-- Checked nominal proof certificate identified upstream as `g_fmpt2`. -/
@[expose]
noncomputable def gFmpt2 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class)
    (D : Class) (F : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv)
    (dv_B_y : y ∉ B.fv) (dv_D_x : x ∉ D.fv) (dv_D_y : y ∉ D.fv) (dv_x_y : x ≠ y)
    (hyp_fmpt2_1 : Nominal.NPrf (.classEq F (synCmpt2 x A y B C))) :
    Nominal.NPrf
      (synWb (synWral x A (synWral y B (.classMem C D))) (synWf F (synCxp A B) D)) :=
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
    @gFmpt2x x y A B C D F dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 hyp_fmpt2_1
  have p0001 := @gIunxpconst x A B dv_cache_0001 dv_cache_0007
  have p0002 :=
    @gFeq2i (synCiun x A (synCxp (synCsn (.cv x)) B)) (synCxp A B) D F p0001
  have p0003 :=
    @gBitri (synWral x A (synWral y B (.classMem C D)))
      (synWf F (synCiun x A (synCxp (synCsn (.cv x)) B)) D) (synWf F (synCxp A B) D)
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

/-- Checked nominal proof certificate identified upstream as `g_fnmpt2`. -/
@[expose]
noncomputable def gFnmpt2 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class)
    (F : Class) (V : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv)
    (dv_B_y : y ∉ B.fv) (dv_x_y : x ≠ y)
    (hyp_fmpt2_1 : Nominal.NPrf (.classEq F (synCmpt2 x A y B C))) :
    Nominal.NPrf
      (.imp (synWral x A (synWral y B (.classMem C V))) (synWfn F (synCxp A B))) :=
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
  have dv_cache_0005 : x ∉ ((synCvv)).fv :=
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
  have dv_cache_0006 : y ∉ ((synCvv)).fv :=
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
  have p0000 := @gElex C V
  have p0001 := @gRalimi (.classMem C V) (.classMem C (synCvv)) y B p0000
  have p0002 :=
    @gRalimi (synWral y B (.classMem C V)) (synWral y B (.classMem C (synCvv))) x A
      p0001
  have p0003 :=
    @gFmpt2 x y A B C (synCvv) F dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007 hyp_fmpt2_1
  have p0004 := @gDffn2 (synCxp A B) F
  have p0005 :=
    @gBitr4i (synWral x A (synWral y B (.classMem C (synCvv))))
      (synWf F (synCxp A B) (synCvv)) (synWfn F (synCxp A B)) p0003 p0004
  have p0006 :=
    @gSylib (synWral x A (synWral y B (.classMem C V)))
      (synWral x A (synWral y B (.classMem C (synCvv)))) (synWfn F (synCxp A B))
      p0002 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_fnmpt2i`. -/
@[expose]
noncomputable def gFnmpt2i (x : Var) (y : Var) (A : Class) (B : Class) (C : Class)
    (F : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv)
    (dv_B_y : y ∉ B.fv) (dv_x_y : x ≠ y)
    (hyp_fmpt2_1 : Nominal.NPrf (.classEq F (synCmpt2 x A y B C)))
    (hyp_fnmpt2i_2 : Nominal.NPrf (.classMem C (synCvv))) :
    Nominal.NPrf (synWfn F (synCxp A B)) :=
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
  have p0000 := @gRgen2w (.classMem C (synCvv)) x y A B hyp_fnmpt2i_2
  have p0001 :=
    @gFnmpt2 x y A B C F (synCvv) dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 hyp_fmpt2_1
  have p0002 := Nominal.mp p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_brsnsi`. -/
@[expose]
noncomputable def gBrsnsi (A : Class) (B : Class) (R : Class)
    (hyp_brsnsi_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_brsnsi_2 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf (synWb (synWbr (synCsn A) (synCsi R) (synCsn B)) (synWbr A R B)) :=
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
  have dv_cache_0001 : x ∉ ((Wff.classEq (.cv z) (synCsn A))).fv := by
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
  have dv_cache_0002 : y ∉ ((Wff.classEq (.cv z) (synCsn A))).fv :=
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
  have dv_cache_0003 : x ∉ ((Wff.classEq (.cv w) (synCsn B))).fv :=
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
  have dv_cache_0004 : y ∉ ((Wff.classEq (.cv w) (synCsn B))).fv :=
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
  have dv_cache_0015 : z ∉ ((synCsn A)).fv :=
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
  have dv_cache_0016 : w ∉ ((synCsn A)).fv :=
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
  have dv_cache_0017 : z ∉ ((synCsn B)).fv :=
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
  have dv_cache_0018 : w ∉ ((synCsn B)).fv :=
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
      ((synWex x (synWex y (synW3a (.classEq (.cv x) A) (.classEq (.cv y) B)
              (synWbr (.cv x) R (.cv y)))))).fv :=
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
      ((synWex x (synWex y (synW3a (.classEq (.cv x) A) (.classEq (.cv y) B)
              (synWbr (.cv x) R (.cv y)))))).fv :=
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
  have dv_cache_0025 : y ∉ ((synWbr A R B)).fv :=
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
  have dv_cache_0026 : x ∉ ((synWbr A R (.cv y))).fv :=
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
  have p0000 := @gSnex A
  have p0001 := @gSnex B
  have p0002 := @gEqeq1 (.cv z) (synCsn A) (synCsn (.cv x))
  have p0003 := @gEqcom (synCsn A) (synCsn (.cv x))
  have p0004 := @gVex x
  have p0005 := @gSneqb (.cv x) A p0004
  have p0006 :=
    @gBitri (.classEq (synCsn A) (synCsn (.cv x)))
      (.classEq (synCsn (.cv x)) (synCsn A)) (.classEq (.cv x) A) p0003 p0005
  have p0007 :=
    @gSyl6bb (.classEq (.cv z) (synCsn A)) (.classEq (.cv z) (synCsn (.cv x)))
      (.classEq (synCsn A) (synCsn (.cv x))) (.classEq (.cv x) A) p0002 p0006
  have p0008 :=
    @gN3anbi1d (.classEq (.cv z) (synCsn A)) (.classEq (.cv z) (synCsn (.cv x)))
      (.classEq (.cv x) A) (.classEq (.cv w) (synCsn (.cv y)))
      (synWbr (.cv x) R (.cv y)) p0007
  have p0009 :=
    @gN2exbidv (.classEq (.cv z) (synCsn A))
      (synW3a (.classEq (.cv z) (synCsn (.cv x))) (.classEq (.cv w) (synCsn (.cv y)))
        (synWbr (.cv x) R (.cv y)))
      (synW3a (.classEq (.cv x) A) (.classEq (.cv w) (synCsn (.cv y)))
        (synWbr (.cv x) R (.cv y)))
      x y dv_cache_0001 dv_cache_0002 p0008
  have p0010 := @gEqeq1 (.cv w) (synCsn B) (synCsn (.cv y))
  have p0011 := @gEqcom (synCsn B) (synCsn (.cv y))
  have p0012 := @gVex y
  have p0013 := @gSneqb (.cv y) B p0012
  have p0014 :=
    @gBitri (.classEq (synCsn B) (synCsn (.cv y)))
      (.classEq (synCsn (.cv y)) (synCsn B)) (.classEq (.cv y) B) p0011 p0013
  have p0015 :=
    @gSyl6bb (.classEq (.cv w) (synCsn B)) (.classEq (.cv w) (synCsn (.cv y)))
      (.classEq (synCsn B) (synCsn (.cv y))) (.classEq (.cv y) B) p0010 p0014
  have p0016 :=
    @gN3anbi2d (.classEq (.cv w) (synCsn B)) (.classEq (.cv w) (synCsn (.cv y)))
      (.classEq (.cv y) B) (.classEq (.cv x) A) (synWbr (.cv x) R (.cv y)) p0015
  have p0017 :=
    @gN2exbidv (.classEq (.cv w) (synCsn B))
      (synW3a (.classEq (.cv x) A) (.classEq (.cv w) (synCsn (.cv y)))
        (synWbr (.cv x) R (.cv y)))
      (synW3a (.classEq (.cv x) A) (.classEq (.cv y) B) (synWbr (.cv x) R (.cv y))) x y
      dv_cache_0003 dv_cache_0004 p0016
  have p0018 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfSi z w x y R
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
      dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
  have p0019 :=
    @gBrab
      (synWex x (synWex y (synW3a (.classEq (.cv z) (synCsn (.cv x)))
            (.classEq (.cv w) (synCsn (.cv y))) (synWbr (.cv x) R (.cv y)))))
      (synWex x (synWex y (synW3a (.classEq (.cv x) A) (.classEq (.cv w) (synCsn (.cv y)))
            (synWbr (.cv x) R (.cv y)))))
      (synWex x (synWex y (synW3a (.classEq (.cv x) A) (.classEq (.cv y) B)
            (synWbr (.cv x) R (.cv y)))))
      z w (synCsn A) (synCsn B) (synCsi R) dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0012 p0000 p0001 p0009 p0017
      p0018
  have p0020 := @gBreq1 (.cv x) A (.cv y) R
  have p0021 := @gBreq2 (.cv y) B A R
  have p0022 :=
    @gCeqsex2v (synWbr (.cv x) R (.cv y)) (synWbr A R (.cv y)) (synWbr A R B) x y A B
      dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026
      dv_cache_0027 hyp_brsnsi_1 hyp_brsnsi_2 p0020 p0021
  have p0023 :=
    @gBitri (synWbr (synCsn A) (synCsi R) (synCsn B))
      (synWex x (synWex y (synW3a (.classEq (.cv x) A) (.classEq (.cv y) B)
            (synWbr (.cv x) R (.cv y)))))
      (synWbr A R B) p0019 p0022
  exact p0023

/-- Checked nominal proof certificate identified upstream as `g_opsnelsi`. -/
@[expose]
noncomputable def gOpsnelsi (A : Class) (B : Class) (R : Class)
    (hyp_brsnsi_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_brsnsi_2 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf
      (synWb (.classMem (synCop (synCsn A) (synCsn B)) (synCsi R))
        (.classMem (synCop A B) R)) :=
  by
  have p0000 := @gBrsnsi A B R hyp_brsnsi_1 hyp_brsnsi_2
  have p0001 := (Nominal.biimpRefl (synWbr (synCsn A) (synCsi R) (synCsn B)))
  have p0002 := (Nominal.biimpRefl (synWbr A R B))
  have p0003 :=
    @gN3bitr3i (synWbr (synCsn A) (synCsi R) (synCsn B)) (synWbr A R B)
      (.classMem (synCop (synCsn A) (synCsn B)) (synCsi R))
      (.classMem (synCop A B) R) p0000 p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_brsnsi1`. -/
@[expose]
noncomputable def gBrsnsi1 (x : Var) (A : Class) (B : Class) (R : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_R_x : x ∉ R.fv)
    (hyp_brsnsi1_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf
      (synWb (synWbr (synCsn A) (synCsi R) B)
        (synWex x (synWa (.classEq B (synCsn (.cv x))) (synWbr A R (.cv x))))) :=
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
  have dv_cache_0001 : y ∉ ((synCsn A)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, fresh_y_not_A,
          not_false_eq_true])
  have dv_cache_0002 : x ∉ ((synCsn A)).fv :=
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
    y ∉ ((synWa (.classEq B (synCsn (.cv x))) (synWbr A R (.cv x)))).fv :=
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
    @gBrsi y x (synCsn A) B R dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0001 :=
    @gExcom
      (synW3a (.classEq (synCsn A) (synCsn (.cv y))) (.classEq B (synCsn (.cv x)))
        (synWbr (.cv y) R (.cv x)))
      y x
  have p0002 := @gEqcom (synCsn A) (synCsn (.cv y))
  have p0003 := @gVex y
  have p0004 := @gSneqb (.cv y) A p0003
  have p0005 :=
    @gBitri (.classEq (synCsn A) (synCsn (.cv y)))
      (.classEq (synCsn (.cv y)) (synCsn A)) (.classEq (.cv y) A) p0002 p0004
  have p0006 :=
    @gN3anbi1i (.classEq (synCsn A) (synCsn (.cv y))) (.classEq (.cv y) A)
      (.classEq B (synCsn (.cv x))) (synWbr (.cv y) R (.cv x)) p0005
  have p0007 :=
    @gN3anass (.classEq (.cv y) A) (.classEq B (synCsn (.cv x)))
      (synWbr (.cv y) R (.cv x))
  have p0008 :=
    @gBitri
      (synW3a (.classEq (synCsn A) (synCsn (.cv y))) (.classEq B (synCsn (.cv x)))
        (synWbr (.cv y) R (.cv x)))
      (synW3a (.classEq (.cv y) A) (.classEq B (synCsn (.cv x))) (synWbr (.cv y) R (.cv x)))
      (synWa (.classEq (.cv y) A)
        (synWa (.classEq B (synCsn (.cv x))) (synWbr (.cv y) R (.cv x))))
      p0006 p0007
  have p0009 :=
    @gExbii
      (synW3a (.classEq (synCsn A) (synCsn (.cv y))) (.classEq B (synCsn (.cv x)))
        (synWbr (.cv y) R (.cv x)))
      (synWa (.classEq (.cv y) A)
        (synWa (.classEq B (synCsn (.cv x))) (synWbr (.cv y) R (.cv x))))
      y p0008
  have p0010 := @gBreq1 (.cv y) A (.cv x) R
  have p0011 :=
    @gAnbi2d (.classEq (.cv y) A) (synWbr (.cv y) R (.cv x)) (synWbr A R (.cv x))
      (.classEq B (synCsn (.cv x))) p0010
  have p0012 :=
    @gCeqsexv (synWa (.classEq B (synCsn (.cv x))) (synWbr (.cv y) R (.cv x)))
      (synWa (.classEq B (synCsn (.cv x))) (synWbr A R (.cv x))) y A dv_cache_0008
      dv_cache_0009 hyp_brsnsi1_1 p0011
  have p0013 :=
    @gBitri
      (synWex y
        (synW3a (.classEq (synCsn A) (synCsn (.cv y))) (.classEq B (synCsn (.cv x)))
          (synWbr (.cv y) R (.cv x))))
      (synWex y (synWa (.classEq (.cv y) A)
          (synWa (.classEq B (synCsn (.cv x))) (synWbr (.cv y) R (.cv x)))))
      (synWa (.classEq B (synCsn (.cv x))) (synWbr A R (.cv x))) p0009 p0012
  have p0014 :=
    @gExbii
      (synWex y
        (synW3a (.classEq (synCsn A) (synCsn (.cv y))) (.classEq B (synCsn (.cv x)))
          (synWbr (.cv y) R (.cv x))))
      (synWa (.classEq B (synCsn (.cv x))) (synWbr A R (.cv x))) x p0013
  have p0015 :=
    @gBitri
      (synWex y (synWex x
          (synW3a (.classEq (synCsn A) (synCsn (.cv y))) (.classEq B (synCsn (.cv x)))
            (synWbr (.cv y) R (.cv x)))))
      (synWex x (synWex y
          (synW3a (.classEq (synCsn A) (synCsn (.cv y))) (.classEq B (synCsn (.cv x)))
            (synWbr (.cv y) R (.cv x)))))
      (synWex x (synWa (.classEq B (synCsn (.cv x))) (synWbr A R (.cv x)))) p0001
      p0014
  have p0016 :=
    @gBitri (synWbr (synCsn A) (synCsi R) B)
      (synWex y (synWex x
          (synW3a (.classEq (synCsn A) (synCsn (.cv y))) (.classEq B (synCsn (.cv x)))
            (synWbr (.cv y) R (.cv x)))))
      (synWex x (synWa (.classEq B (synCsn (.cv x))) (synWbr A R (.cv x)))) p0000
      p0015
  exact p0016

/-- Checked nominal proof certificate identified upstream as `g_brsnsi2`. -/
@[expose]
noncomputable def gBrsnsi2 (x : Var) (A : Class) (B : Class) (R : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_R_x : x ∉ R.fv)
    (hyp_brsnsi1_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf
      (synWb (synWbr B (synCsi R) (synCsn A))
        (synWex x (synWa (.classEq B (synCsn (.cv x))) (synWbr (.cv x) R A)))) :=
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
  have dv_cache_0003 : x ∉ ((synCsn A)).fv :=
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
  have dv_cache_0004 : y ∉ ((synCsn A)).fv :=
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
  have dv_cache_0008 : y ∉ ((Wff.classEq B (synCsn (.cv x)))).fv :=
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
  have dv_cache_0010 : y ∉ ((synWbr (.cv x) R A)).fv :=
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
    @gBrsi x y B (synCsn A) R dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0001 :=
    @gN3anass (.classEq B (synCsn (.cv x))) (.classEq (synCsn A) (synCsn (.cv y)))
      (synWbr (.cv x) R (.cv y))
  have p0002 :=
    @gExbii
      (synW3a (.classEq B (synCsn (.cv x))) (.classEq (synCsn A) (synCsn (.cv y)))
        (synWbr (.cv x) R (.cv y)))
      (synWa (.classEq B (synCsn (.cv x)))
        (synWa (.classEq (synCsn A) (synCsn (.cv y))) (synWbr (.cv x) R (.cv y))))
      y p0001
  have p0003 :=
    @gN1942v (.classEq B (synCsn (.cv x)))
      (synWa (.classEq (synCsn A) (synCsn (.cv y))) (synWbr (.cv x) R (.cv y))) y
      dv_cache_0008
  have p0004 := @gSneqb A (.cv y) hyp_brsnsi1_1
  have p0005 := @gEqcom A (.cv y)
  have p0006 :=
    @gBitri (.classEq (synCsn A) (synCsn (.cv y))) (.classEq A (.cv y))
      (.classEq (.cv y) A) p0004 p0005
  have p0007 :=
    @gAnbi1i (.classEq (synCsn A) (synCsn (.cv y))) (.classEq (.cv y) A)
      (synWbr (.cv x) R (.cv y)) p0006
  have p0008 :=
    @gExbii (synWa (.classEq (synCsn A) (synCsn (.cv y))) (synWbr (.cv x) R (.cv y)))
      (synWa (.classEq (.cv y) A) (synWbr (.cv x) R (.cv y))) y p0007
  have p0009 := @gBreq2 (.cv y) A (.cv x) R
  have p0010 :=
    @gCeqsexv (synWbr (.cv x) R (.cv y)) (synWbr (.cv x) R A) y A dv_cache_0009
      dv_cache_0010 hyp_brsnsi1_1 p0009
  have p0011 :=
    @gBitri
      (synWex y (synWa (.classEq (synCsn A) (synCsn (.cv y))) (synWbr (.cv x) R (.cv y))))
      (synWex y (synWa (.classEq (.cv y) A) (synWbr (.cv x) R (.cv y))))
      (synWbr (.cv x) R A) p0008 p0010
  have p0012 :=
    @gAnbi2i
      (synWex y (synWa (.classEq (synCsn A) (synCsn (.cv y))) (synWbr (.cv x) R (.cv y))))
      (synWbr (.cv x) R A) (.classEq B (synCsn (.cv x))) p0011
  have p0013 :=
    @gBitri
      (synWex y (synWa (.classEq B (synCsn (.cv x)))
          (synWa (.classEq (synCsn A) (synCsn (.cv y))) (synWbr (.cv x) R (.cv y)))))
      (synWa (.classEq B (synCsn (.cv x))) (synWex y
          (synWa (.classEq (synCsn A) (synCsn (.cv y))) (synWbr (.cv x) R (.cv y)))))
      (synWa (.classEq B (synCsn (.cv x))) (synWbr (.cv x) R A)) p0003 p0012
  have p0014 :=
    @gBitri
      (synWex y
        (synW3a (.classEq B (synCsn (.cv x))) (.classEq (synCsn A) (synCsn (.cv y)))
          (synWbr (.cv x) R (.cv y))))
      (synWex y (synWa (.classEq B (synCsn (.cv x)))
          (synWa (.classEq (synCsn A) (synCsn (.cv y))) (synWbr (.cv x) R (.cv y)))))
      (synWa (.classEq B (synCsn (.cv x))) (synWbr (.cv x) R A)) p0002 p0013
  have p0015 :=
    @gExbii
      (synWex y
        (synW3a (.classEq B (synCsn (.cv x))) (.classEq (synCsn A) (synCsn (.cv y)))
          (synWbr (.cv x) R (.cv y))))
      (synWa (.classEq B (synCsn (.cv x))) (synWbr (.cv x) R A)) x p0014
  have p0016 :=
    @gBitri (synWbr B (synCsi R) (synCsn A))
      (synWex x (synWex y
          (synW3a (.classEq B (synCsn (.cv x))) (.classEq (synCsn A) (synCsn (.cv y)))
            (synWbr (.cv x) R (.cv y)))))
      (synWex x (synWa (.classEq B (synCsn (.cv x))) (synWbr (.cv x) R A))) p0000
      p0015
  exact p0016

/-- Checked nominal proof certificate identified upstream as `g_brco1st`. -/
@[expose]
noncomputable def gBrco1st (A : Class) (B : Class) (C : Class) (R : Class)
    (hyp_brco1st_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_brco1st_2 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf
      (synWb (synWbr (synCop A B) (synCcom R (synC1st)) C) (synWbr A R C)) :=
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
  have dv_cache_0001 : x ∉ ((synCop A B)).fv := by
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
  have dv_cache_0004 : x ∉ ((synC1st)).fv :=
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
  have dv_cache_0006 : x ∉ ((synWbr A R C)).fv :=
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
    @gBrco x (synCop A B) C R (synC1st) dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004
  have p0001 := @gOpbr1st A B (.cv x) hyp_brco1st_1 hyp_brco1st_2
  have p0002 := @gEqcom A (.cv x)
  have p0003 :=
    @gBitri (synWbr (synCop A B) (synC1st) (.cv x)) (.classEq A (.cv x))
      (.classEq (.cv x) A) p0001 p0002
  have p0004 :=
    @gAnbi1i (synWbr (synCop A B) (synC1st) (.cv x)) (.classEq (.cv x) A)
      (synWbr (.cv x) R C) p0003
  have p0005 :=
    @gExbii (synWa (synWbr (synCop A B) (synC1st) (.cv x)) (synWbr (.cv x) R C))
      (synWa (.classEq (.cv x) A) (synWbr (.cv x) R C)) x p0004
  have p0006 := @gBreq1 (.cv x) A C R
  have p0007 :=
    @gCeqsexv (synWbr (.cv x) R C) (synWbr A R C) x A dv_cache_0005 dv_cache_0006
      hyp_brco1st_1 p0006
  have p0008 :=
    @gN3bitri (synWbr (synCop A B) (synCcom R (synC1st)) C)
      (synWex x (synWa (synWbr (synCop A B) (synC1st) (.cv x)) (synWbr (.cv x) R C)))
      (synWex x (synWa (.classEq (.cv x) A) (synWbr (.cv x) R C))) (synWbr A R C)
      p0000 p0005 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_brco2nd`. -/
@[expose]
noncomputable def gBrco2nd (A : Class) (B : Class) (C : Class) (R : Class)
    (hyp_brco1st_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_brco1st_2 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf
      (synWb (synWbr (synCop A B) (synCcom R (synC2nd)) C) (synWbr B R C)) :=
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
  have dv_cache_0001 : x ∉ ((synCop A B)).fv := by
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
  have dv_cache_0004 : x ∉ ((synC2nd)).fv :=
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
  have dv_cache_0006 : x ∉ ((synWbr B R C)).fv :=
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
    @gBrco x (synCop A B) C R (synC2nd) dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004
  have p0001 := @gOpbr2nd A B (.cv x) hyp_brco1st_1 hyp_brco1st_2
  have p0002 := @gEqcom B (.cv x)
  have p0003 :=
    @gBitri (synWbr (synCop A B) (synC2nd) (.cv x)) (.classEq B (.cv x))
      (.classEq (.cv x) B) p0001 p0002
  have p0004 :=
    @gAnbi1i (synWbr (synCop A B) (synC2nd) (.cv x)) (.classEq (.cv x) B)
      (synWbr (.cv x) R C) p0003
  have p0005 :=
    @gExbii (synWa (synWbr (synCop A B) (synC2nd) (.cv x)) (synWbr (.cv x) R C))
      (synWa (.classEq (.cv x) B) (synWbr (.cv x) R C)) x p0004
  have p0006 := @gBreq1 (.cv x) B C R
  have p0007 :=
    @gCeqsexv (synWbr (.cv x) R C) (synWbr B R C) x B dv_cache_0005 dv_cache_0006
      hyp_brco1st_2 p0006
  have p0008 :=
    @gN3bitri (synWbr (synCop A B) (synCcom R (synC2nd)) C)
      (synWex x (synWa (synWbr (synCop A B) (synC2nd) (.cv x)) (synWbr (.cv x) R C)))
      (synWex x (synWa (.classEq (.cv x) B) (synWbr (.cv x) R C))) (synWbr B R C)
      p0000 p0005 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_txpeq2`. -/
@[expose]
noncomputable def gTxpeq2 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (synCtxp C A) (synCtxp C B))) :=
  by
  have p0000 := @gCoeq2 A B (synCcnv (synC2nd))
  have p0001 :=
    @gIneq2d (.classEq A B) (synCcom (synCcnv (synC2nd)) A)
      (synCcom (synCcnv (synC2nd)) B) (synCcom (synCcnv (synC1st)) C) p0000
  have p0002 := (Nominal.classEqRefl (synCtxp C A))
  have p0003 := (Nominal.classEqRefl (synCtxp C B))
  have p0004 :=
    @gN3eqtr4g (.classEq A B)
      (synCin (synCcom (synCcnv (synC1st)) C) (synCcom (synCcnv (synC2nd)) A))
      (synCin (synCcom (synCcnv (synC1st)) C) (synCcom (synCcnv (synC2nd)) B))
      (synCtxp C A) (synCtxp C B) p0001 p0002 p0003
  exact p0004


end NFChoice.DirectNominalPrf.WPPReplay

end

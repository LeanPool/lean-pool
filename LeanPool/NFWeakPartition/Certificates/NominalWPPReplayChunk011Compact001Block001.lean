/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk010Compact001Block020

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk011Compact001Part001`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_coeq2i`. -/
@[expose]
noncomputable def gCoeq2i (A : Class) (B : Class) (C : Class)
    (hyp_coeq1i_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (.classEq (synCcom C A) (synCcom C B)) :=
  by
  have p0000 := @gCoeq2 A B C
  have p0001 := Nominal.mp hyp_coeq1i_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_coeq1d`. -/
@[expose]
noncomputable def gCoeq1d (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_coeq1d_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (synCcom A C) (synCcom B C))) :=
  by
  have p0000 := @gCoeq1 A B C
  have p0001 :=
    @gSyl ph (.classEq A B) (.classEq (synCcom A C) (synCcom B C)) hyp_coeq1d_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_coeq2d`. -/
@[expose]
noncomputable def gCoeq2d (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_coeq1d_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (synCcom C A) (synCcom C B))) :=
  by
  have p0000 := @gCoeq2 A B C
  have p0001 :=
    @gSyl ph (.classEq A B) (.classEq (synCcom C A) (synCcom C B)) hyp_coeq1d_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_coeq12i`. -/
@[expose]
noncomputable def gCoeq12i (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_coeq12i_1 : Nominal.NPrf (.classEq A B))
    (hyp_coeq12i_2 : Nominal.NPrf (.classEq C D)) :
    Nominal.NPrf (.classEq (synCcom A C) (synCcom B D)) :=
  by
  have p0000 := @gCoeq1i A B C hyp_coeq12i_1
  have p0001 := @gCoeq2i C D B hyp_coeq12i_2
  have p0002 := @gEqtri (synCcom A C) (synCcom B C) (synCcom B D) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_coeq12d`. -/
@[expose]
noncomputable def gCoeq12d (ph : Wff) (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_coeq12d_1 : Nominal.NPrf (.imp ph (.classEq A B)))
    (hyp_coeq12d_2 : Nominal.NPrf (.imp ph (.classEq C D))) :
    Nominal.NPrf (.imp ph (.classEq (synCcom A C) (synCcom B D))) :=
  by
  have p0000 := @gCoeq1d ph A B C hyp_coeq12d_1
  have p0001 := @gCoeq2d ph C D B hyp_coeq12d_2
  have p0002 := @gEqtrd ph (synCcom A C) (synCcom B C) (synCcom B D) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_brco`. -/
@[expose]
noncomputable def gBrco (x : Var) (A : Class) (B : Class) (C : Class) (D : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_C_x : x ∉ C.fv) (dv_D_x : x ∉ D.fv) :
    Nominal.NPrf
      (synWb (synWbr A (synCcom C D) B)
        (synWex x (synWa (synWbr A D (.cv x)) (synWbr (.cv x) C B)))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv ∪ D.fv
  let y : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
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
  have fresh_y_not_D : y ∉ D.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_not_C : z ∉ C.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_D : z ∉ D.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 :
    x ∉ ((synWa (.classMem A (synCvv)) (.classMem B (synCvv)))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, dv_A_x,
          dv_B_x, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((Wff.classEq (.cv y) A)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_y, dv_A_x, or_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((Wff.classEq (.cv z) B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_z, dv_B_x, or_false, not_false_eq_true])
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
  have dv_cache_0005 : z ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_C, not_false_eq_true])
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
  have dv_cache_0007 : y ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_D, not_false_eq_true])
  have dv_cache_0008 : z ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_D, not_false_eq_true])
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
  have dv_cache_0010 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0011 : y ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show y ≠ x from (by exact fresh_y_ne_x))
  have dv_cache_0012 : z ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show z ≠ x from (by exact fresh_z_ne_x))
  have dv_cache_0013 : y ∉ (A).fv :=
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
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0014 : z ∉ (A).fv :=
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
        simp only [fresh_z_not_A, not_false_eq_true])
  have dv_cache_0015 : y ∉ (B).fv :=
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
        simp only [fresh_y_not_B, not_false_eq_true])
  have dv_cache_0016 : z ∉ (B).fv :=
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
        simp only [fresh_z_not_B, not_false_eq_true])
  have dv_cache_0017 :
    y ∉ ((synWex x (synWa (synWbr A D (.cv x)) (synWbr (.cv x) C B)))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_y_not_A, fresh_y_ne_x, fresh_y_not_D, fresh_y_not_B,
          fresh_y_not_C, or_false, and_false, not_false_eq_true])
  have dv_cache_0018 :
    z ∉ ((synWex x (synWa (synWbr A D (.cv x)) (synWbr (.cv x) C B)))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_z_not_A, fresh_z_ne_x, fresh_z_not_D, fresh_z_not_B,
          fresh_z_not_C, or_false, and_false, not_false_eq_true])
  have p0000 := @gBrex A B (synCcom C D)
  have p0001 := @gBrex A (.cv x) D
  have p0002 :=
    @gSimpld (synWbr A D (.cv x)) (.classMem A (synCvv)) (.classMem (.cv x) (synCvv))
      p0001
  have p0003 := @gBrex (.cv x) B C
  have p0004 :=
    @gSimprd (synWbr (.cv x) C B) (.classMem (.cv x) (synCvv)) (.classMem B (synCvv))
      p0003
  have p0005 :=
    @gAnim12i (synWbr A D (.cv x)) (.classMem A (synCvv)) (synWbr (.cv x) C B)
      (.classMem B (synCvv)) p0002 p0004
  have p0006 :=
    @gExlimiv (synWa (synWbr A D (.cv x)) (synWbr (.cv x) C B))
      (synWa (.classMem A (synCvv)) (.classMem B (synCvv))) x dv_cache_0001 p0005
  have p0007 := @gBreq1 (.cv y) A (.cv x) D
  have p0008 :=
    @gAnbi1d (.classEq (.cv y) A) (synWbr (.cv y) D (.cv x)) (synWbr A D (.cv x))
      (synWbr (.cv x) C (.cv z)) p0007
  have p0009 :=
    @gExbidv (.classEq (.cv y) A)
      (synWa (synWbr (.cv y) D (.cv x)) (synWbr (.cv x) C (.cv z)))
      (synWa (synWbr A D (.cv x)) (synWbr (.cv x) C (.cv z))) x dv_cache_0002 p0008
  have p0010 := @gBreq2 (.cv z) B (.cv x) C
  have p0011 :=
    @gAnbi2d (.classEq (.cv z) B) (synWbr (.cv x) C (.cv z)) (synWbr (.cv x) C B)
      (synWbr A D (.cv x)) p0010
  have p0012 :=
    @gExbidv (.classEq (.cv z) B)
      (synWa (synWbr A D (.cv x)) (synWbr (.cv x) C (.cv z)))
      (synWa (synWbr A D (.cv x)) (synWbr (.cv x) C B)) x dv_cache_0003 p0011
  have p0013 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfCo y z x C D
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
      dv_cache_0010 dv_cache_0011 dv_cache_0012
  have p0014 :=
    @gBrabg (synWex x (synWa (synWbr (.cv y) D (.cv x)) (synWbr (.cv x) C (.cv z))))
      (synWex x (synWa (synWbr A D (.cv x)) (synWbr (.cv x) C (.cv z))))
      (synWex x (synWa (synWbr A D (.cv x)) (synWbr (.cv x) C B))) y z A B (synCvv)
      (synCvv) (synCcom C D) dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
      dv_cache_0017 dv_cache_0018 dv_cache_0010 p0009 p0012 p0013
  have p0015 :=
    @gPm521nii (synWbr A (synCcom C D) B)
      (synWa (.classMem A (synCvv)) (.classMem B (synCvv)))
      (synWex x (synWa (synWbr A D (.cv x)) (synWbr (.cv x) C B))) p0000 p0006 p0014
  exact p0015

/-- Checked nominal proof certificate identified upstream as `g_opelco`. -/
@[expose]
noncomputable def gOpelco (x : Var) (A : Class) (B : Class) (C : Class) (D : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_C_x : x ∉ C.fv) (dv_D_x : x ∉ D.fv) :
    Nominal.NPrf
      (synWb (.classMem (synCop A B) (synCcom C D))
        (synWex x (synWa (synWbr A D (.cv x)) (synWbr (.cv x) C B)))) :=
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
  have p0000 := (Nominal.biimpRefl (synWbr A (synCcom C D) B))
  have p0001 := @gBrco x A B C D dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0002 :=
    @gBitr3i (.classMem (synCop A B) (synCcom C D)) (synWbr A (synCcom C D) B)
      (synWex x (synWa (synWbr A D (.cv x)) (synWbr (.cv x) C B))) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_cnvss`. -/
@[expose]
noncomputable def gCnvss (A : Class) (B : Class) :
    Nominal.NPrf (.imp (synWss A B) (synWss (synCcnv A) (synCcnv B))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let y : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y_ne_x : y ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have dv_cache_0001 : x ∉ ((synWss A B)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((synWss A B)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union,
          fresh_y_not_A, fresh_y_not_B, or_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
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
  have dv_cache_0006 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_B, not_false_eq_true])
  have dv_cache_0007 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_B, not_false_eq_true])
  have p0000 := @gSsel A B (synCop (.cv y) (.cv x))
  have p0001 := (Nominal.biimpRefl (synWbr (.cv y) A (.cv x)))
  have p0002 := (Nominal.biimpRefl (synWbr (.cv y) B (.cv x)))
  have p0003 :=
    @gN3imtr4g (synWss A B) (.classMem (synCop (.cv y) (.cv x)) A)
      (.classMem (synCop (.cv y) (.cv x)) B) (synWbr (.cv y) A (.cv x))
      (synWbr (.cv y) B (.cv x)) p0000 p0001 p0002
  have p0004 :=
    @gSsopab2dv (synWss A B) (synWbr (.cv y) A (.cv x)) (synWbr (.cv y) B (.cv x)) x y
      dv_cache_0001 dv_cache_0002 p0003
  have p0005 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfCnv x y A
      dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0006 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfCnv x y B
      dv_cache_0006 dv_cache_0007 dv_cache_0005
  have p0007 :=
    @gN3sstr4g (synWss A B) (synCopab x y (synWbr (.cv y) A (.cv x)))
      (synCopab x y (synWbr (.cv y) B (.cv x))) (synCcnv A) (synCcnv B) p0004 p0005
      p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_cnveq`. -/
@[expose]
noncomputable def gCnveq (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (synCcnv A) (synCcnv B))) :=
  by
  have p0000 := @gCnvss A B
  have p0001 := @gCnvss B A
  have p0002 :=
    @gAnim12i (synWss A B) (synWss (synCcnv A) (synCcnv B)) (synWss B A)
      (synWss (synCcnv B) (synCcnv A)) p0000 p0001
  have p0003 := @gEqss A B
  have p0004 := @gEqss (synCcnv A) (synCcnv B)
  have p0005 :=
    @gN3imtr4i (synWa (synWss A B) (synWss B A))
      (synWa (synWss (synCcnv A) (synCcnv B)) (synWss (synCcnv B) (synCcnv A)))
      (.classEq A B) (.classEq (synCcnv A) (synCcnv B)) p0002 p0003 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_cnveqi`. -/
@[expose]
noncomputable def gCnveqi (A : Class) (B : Class)
    (hyp_cnveqi_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (.classEq (synCcnv A) (synCcnv B)) :=
  by
  have p0000 := @gCnveq A B
  have p0001 := Nominal.mp hyp_cnveqi_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_cnveqd`. -/
@[expose]
noncomputable def gCnveqd (ph : Wff) (A : Class) (B : Class)
    (hyp_cnveqd_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (synCcnv A) (synCcnv B))) :=
  by
  have p0000 := @gCnveq A B
  have p0001 :=
    @gSyl ph (.classEq A B) (.classEq (synCcnv A) (synCcnv B)) hyp_cnveqd_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_elcnv`. -/
@[expose]
noncomputable def gElcnv (x : Var) (y : Var) (A : Class) (R : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_R_x : x ∉ R.fv) (dv_R_y : y ∉ R.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (synWb (.classMem A (synCcnv R)) (synWex x (synWex y
            (synWa (.classEq A (synCop (.cv x) (.cv y))) (synWbr (.cv y) R (.cv x)))))) :=
  by
  have dv_cache_0001 : x ∉ (R).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_x, not_false_eq_true])
  have dv_cache_0002 : y ∉ (R).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_y, not_false_eq_true])
  have dv_cache_0003 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show x ≠ y from (by exact dv_x_y))
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
        simp only [dv_A_y, not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfCnv x y R
      dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 := @gEleq2i (synCcnv R) (synCopab x y (synWbr (.cv y) R (.cv x))) A p0000
  have p0002 := @gElopab (synWbr (.cv y) R (.cv x)) x y A dv_cache_0004 dv_cache_0005
  have p0003 :=
    @gBitri (.classMem A (synCcnv R))
      (.classMem A (synCopab x y (synWbr (.cv y) R (.cv x))))
      (synWex x (synWex y
          (synWa (.classEq A (synCop (.cv x) (.cv y))) (synWbr (.cv y) R (.cv x)))))
      p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_elcnv2`. -/
@[expose]
noncomputable def gElcnv2 (x : Var) (y : Var) (A : Class) (R : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_R_x : x ∉ R.fv) (dv_R_y : y ∉ R.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (synWb (.classMem A (synCcnv R)) (synWex x (synWex y
            (synWa (.classEq A (synCop (.cv x) (.cv y)))
              (.classMem (synCop (.cv y) (.cv x)) R))))) :=
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
  have dv_cache_0003 : x ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_x, not_false_eq_true])
  have dv_cache_0004 : y ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_y, not_false_eq_true])
  have dv_cache_0005 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ y from (by exact dv_x_y))
  have p0000 :=
    @gElcnv x y A R dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0001 := (Nominal.biimpRefl (synWbr (.cv y) R (.cv x)))
  have p0002 :=
    @gAnbi2i (synWbr (.cv y) R (.cv x)) (.classMem (synCop (.cv y) (.cv x)) R)
      (.classEq A (synCop (.cv x) (.cv y))) p0001
  have p0003 :=
    @gN2exbii
      (synWa (.classEq A (synCop (.cv x) (.cv y))) (synWbr (.cv y) R (.cv x)))
      (synWa (.classEq A (synCop (.cv x) (.cv y))) (.classMem (synCop (.cv y) (.cv x)) R))
      x y p0002
  have p0004 :=
    @gBitri (.classMem A (synCcnv R))
      (synWex x (synWex y
          (synWa (.classEq A (synCop (.cv x) (.cv y))) (synWbr (.cv y) R (.cv x)))))
      (synWex x (synWex y (synWa (.classEq A (synCop (.cv x) (.cv y)))
            (.classMem (synCop (.cv y) (.cv x)) R))))
      p0000 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_brcnv`. -/
@[expose]
noncomputable def gBrcnv (A : Class) (B : Class) (R : Class) :
    Nominal.NPrf (synWb (synWbr A (synCcnv R) B) (synWbr B R A)) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ R.fv
  let y : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y_ne_x : y ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have dv_cache_0001 : x ∉ (R).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_R, not_false_eq_true])
  have dv_cache_0002 : y ∉ (R).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_R, not_false_eq_true])
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
        simp only [fresh_x_not_A, not_false_eq_true])
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
  have dv_cache_0006 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_B, not_false_eq_true])
  have dv_cache_0007 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_B, not_false_eq_true])
  have dv_cache_0008 : x ∉ ((synWbr B R A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          fresh_x_not_B, fresh_x_not_A, fresh_x_not_R, or_false, not_false_eq_true])
  have dv_cache_0009 : y ∉ ((synWbr B R A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          fresh_y_not_B, fresh_y_not_A, fresh_y_not_R, or_false, not_false_eq_true])
  have p0000 := @gBrex A B (synCcnv R)
  have p0001 := @gBrex B A R
  have p0002 :=
    @gAncomd (synWbr B R A) (.classMem B (synCvv)) (.classMem A (synCvv)) p0001
  have p0003 := @gBreq2 (.cv x) A (.cv y) R
  have p0004 := @gBreq1 (.cv y) B A R
  have p0005 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfCnv x y R
      dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0006 :=
    @gBrabg (synWbr (.cv y) R (.cv x)) (synWbr (.cv y) R A) (synWbr B R A) x y A B
      (synCvv) (synCvv) (synCcnv R) dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0003 p0003 p0004 p0005
  have p0007 :=
    @gPm521nii (synWbr A (synCcnv R) B)
      (synWa (.classMem A (synCvv)) (.classMem B (synCvv))) (synWbr B R A) p0000 p0002
      p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_opelcnv`. -/
@[expose]
noncomputable def gOpelcnv (A : Class) (B : Class) (R : Class) :
    Nominal.NPrf
      (synWb (.classMem (synCop A B) (synCcnv R)) (.classMem (synCop B A) R)) :=
  by
  have p0000 := @gBrcnv A B R
  have p0001 := (Nominal.biimpRefl (synWbr A (synCcnv R) B))
  have p0002 := (Nominal.biimpRefl (synWbr B R A))
  have p0003 :=
    @gN3bitr3i (synWbr A (synCcnv R) B) (synWbr B R A)
      (.classMem (synCop A B) (synCcnv R)) (.classMem (synCop B A) R) p0000 p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_cnvco`. -/
@[expose]
noncomputable def gCnvco (A : Class) (B : Class) :
    Nominal.NPrf
      (.classEq (synCcnv (synCcom A B)) (synCcom (synCcnv B) (synCcnv A))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
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
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (h))
  have fresh_z_not_B : z ∉ B.fv := by
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
  have dv_cache_0001 : z ∉ ((Class.cv x)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_x, not_false_eq_true])
  have dv_cache_0002 : z ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_y, not_false_eq_true])
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
  have dv_cache_0004 : z ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_B, not_false_eq_true])
  have dv_cache_0005 : y ∉ ((synCcom A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          Finset.mem_union, fresh_y_not_A, fresh_y_not_B, or_false, not_false_eq_true])
  have dv_cache_0006 : x ∉ ((synCcom A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          Finset.mem_union, fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true])
  have dv_cache_0007 : y ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show y ≠ x from (by exact fresh_y_ne_x))
  have dv_cache_0008 : y ∉ ((synCcnv B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, fresh_y_not_B,
          not_false_eq_true])
  have dv_cache_0009 : x ∉ ((synCcnv B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, fresh_x_not_B,
          not_false_eq_true])
  have dv_cache_0010 : z ∉ ((synCcnv B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, fresh_z_not_B,
          not_false_eq_true])
  have dv_cache_0011 : y ∉ ((synCcnv A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, fresh_y_not_A,
          not_false_eq_true])
  have dv_cache_0012 : x ∉ ((synCcnv A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, fresh_x_not_A,
          not_false_eq_true])
  have dv_cache_0013 : z ∉ ((synCcnv A)).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, fresh_z_not_A,
          not_false_eq_true])
  have dv_cache_0014 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0015 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have p0000 :=
    @gBrco z (.cv x) (.cv y) A B dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0001 := @gBrcnv (.cv z) (.cv x) B
  have p0002 := @gBrcnv (.cv y) (.cv z) A
  have p0003 :=
    @gAnbi12i (synWbr (.cv z) (synCcnv B) (.cv x)) (synWbr (.cv x) B (.cv z))
      (synWbr (.cv y) (synCcnv A) (.cv z)) (synWbr (.cv z) A (.cv y)) p0001 p0002
  have p0004 :=
    @gAncom (synWbr (.cv z) (synCcnv B) (.cv x)) (synWbr (.cv y) (synCcnv A) (.cv z))
  have p0005 :=
    @gBitr3i (synWa (synWbr (.cv x) B (.cv z)) (synWbr (.cv z) A (.cv y)))
      (synWa (synWbr (.cv z) (synCcnv B) (.cv x)) (synWbr (.cv y) (synCcnv A) (.cv z)))
      (synWa (synWbr (.cv y) (synCcnv A) (.cv z)) (synWbr (.cv z) (synCcnv B) (.cv x)))
      p0003 p0004
  have p0006 :=
    @gExbii (synWa (synWbr (.cv x) B (.cv z)) (synWbr (.cv z) A (.cv y)))
      (synWa (synWbr (.cv y) (synCcnv A) (.cv z)) (synWbr (.cv z) (synCcnv B) (.cv x)))
      z p0005
  have p0007 :=
    @gBitri (synWbr (.cv x) (synCcom A B) (.cv y))
      (synWex z (synWa (synWbr (.cv x) B (.cv z)) (synWbr (.cv z) A (.cv y))))
      (synWex z (synWa (synWbr (.cv y) (synCcnv A) (.cv z))
          (synWbr (.cv z) (synCcnv B) (.cv x))))
      p0000 p0006
  have p0008 :=
    @gOpabbii (synWbr (.cv x) (synCcom A B) (.cv y))
      (synWex z (synWa (synWbr (.cv y) (synCcnv A) (.cv z))
          (synWbr (.cv z) (synCcnv B) (.cv x))))
      y x p0007
  have p0009 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfCnv y x
      (synCcom A B) dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0010 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfCo y x z
      (synCcnv B) (synCcnv A) dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0007 dv_cache_0014 dv_cache_0015
  have p0011 :=
    @gN3eqtr4i (synCopab y x (synWbr (.cv x) (synCcom A B) (.cv y)))
      (synCopab y x (synWex z (synWa (synWbr (.cv y) (synCcnv A) (.cv z))
            (synWbr (.cv z) (synCcnv B) (.cv x)))))
      (synCcnv (synCcom A B)) (synCcom (synCcnv B) (synCcnv A)) p0008 p0009 p0010
  exact p0011


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk011Compact001Part002`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_cnvuni`. -/
@[expose]
noncomputable def gCnvuni (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (.classEq (synCcnv (synCuni A)) (synCiun x A (synCcnv (.cv x)))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv
  let y : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  let w : Var := freshVar proofSupport 2
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
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
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
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_z_ne_y : z ≠ y := Ne.symm fresh_y_ne_z
  have fresh_y_ne_w : y ≠ w :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_w_ne_y : w ≠ y := Ne.symm fresh_y_ne_w
  have fresh_z_ne_w : z ≠ w :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have dv_cache_0001 : z ∉ ((Class.cv y)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_y, not_false_eq_true])
  have dv_cache_0002 : w ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_w_ne_y, not_false_eq_true])
  have dv_cache_0003 : z ∉ ((synCuni A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, fresh_z_not_A,
          not_false_eq_true])
  have dv_cache_0004 : w ∉ ((synCuni A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, fresh_w_not_A,
          not_false_eq_true])
  have dv_cache_0005 : z ≠ w :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show z ≠ w from (by exact fresh_z_ne_w))
  have dv_cache_0006 : x ∉ ((synCop (.cv w) (.cv z))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_w, fresh_x_ne_z, or_false, not_false_eq_true])
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
  have dv_cache_0008 : x ∉ ((Wff.classEq (.cv y) (synCop (.cv z) (.cv w)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_y, fresh_x_ne_z, fresh_x_ne_w, or_false,
          not_false_eq_true])
  have dv_cache_0009 : z ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_x, not_false_eq_true])
  have dv_cache_0010 : w ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_w_ne_x, not_false_eq_true])
  have dv_cache_0011 : z ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_A, not_false_eq_true])
  have dv_cache_0012 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0013 : w ∉ (A).fv :=
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
        simp only [fresh_w_not_A, not_false_eq_true])
  have dv_cache_0014 : x ≠ w :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact (show x ≠ w from (by exact fresh_x_ne_w))
  have dv_cache_0015 : x ∉ ((Class.cv y)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_y, not_false_eq_true])
  have dv_cache_0016 : y ∉ ((synCcnv (synCuni A))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, fresh_y_not_A,
          not_false_eq_true])
  have dv_cache_0017 : y ∉ ((synCiun x A (synCcnv (.cv x)))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ciun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_y_not_A, fresh_y_ne_x, or_false, and_false,
          not_false_eq_true])
  have p0000 :=
    @gElcnv2 z w (.cv y) (synCuni A) dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005
  have p0001 := @gEluni2 x (synCop (.cv w) (.cv z)) A dv_cache_0006 dv_cache_0007
  have p0002 :=
    @gAnbi2i (.classMem (synCop (.cv w) (.cv z)) (synCuni A))
      (synWrex x A (.classMem (synCop (.cv w) (.cv z)) (.cv x)))
      (.classEq (.cv y) (synCop (.cv z) (.cv w))) p0001
  have p0003 :=
    @gR1942v (.classEq (.cv y) (synCop (.cv z) (.cv w)))
      (.classMem (synCop (.cv w) (.cv z)) (.cv x)) x A dv_cache_0008
  have p0004 :=
    @gBitr4i
      (synWa (.classEq (.cv y) (synCop (.cv z) (.cv w)))
        (.classMem (synCop (.cv w) (.cv z)) (synCuni A)))
      (synWa (.classEq (.cv y) (synCop (.cv z) (.cv w)))
        (synWrex x A (.classMem (synCop (.cv w) (.cv z)) (.cv x))))
      (synWrex x A (synWa (.classEq (.cv y) (synCop (.cv z) (.cv w)))
          (.classMem (synCop (.cv w) (.cv z)) (.cv x))))
      p0002 p0003
  have p0005 :=
    @gN2exbii
      (synWa (.classEq (.cv y) (synCop (.cv z) (.cv w)))
        (.classMem (synCop (.cv w) (.cv z)) (synCuni A)))
      (synWrex x A (synWa (.classEq (.cv y) (synCop (.cv z) (.cv w)))
          (.classMem (synCop (.cv w) (.cv z)) (.cv x))))
      z w p0004
  have p0006 :=
    @gElcnv2 z w (.cv y) (.cv x) dv_cache_0001 dv_cache_0002 dv_cache_0009 dv_cache_0010
      dv_cache_0005
  have p0007 :=
    @gRexbii (.classMem (.cv y) (synCcnv (.cv x)))
      (synWex z (synWex w (synWa (.classEq (.cv y) (synCop (.cv z) (.cv w)))
            (.classMem (synCop (.cv w) (.cv z)) (.cv x)))))
      x A p0006
  have p0008 :=
    @gRexcom4
      (synWex w (synWa (.classEq (.cv y) (synCop (.cv z) (.cv w)))
          (.classMem (synCop (.cv w) (.cv z)) (.cv x))))
      x z A dv_cache_0011 dv_cache_0012
  have p0009 :=
    @gRexcom4
      (synWa (.classEq (.cv y) (synCop (.cv z) (.cv w)))
        (.classMem (synCop (.cv w) (.cv z)) (.cv x)))
      x w A dv_cache_0013 dv_cache_0014
  have p0010 :=
    @gExbii
      (synWrex x A (synWex w (synWa (.classEq (.cv y) (synCop (.cv z) (.cv w)))
            (.classMem (synCop (.cv w) (.cv z)) (.cv x)))))
      (synWex w (synWrex x A (synWa (.classEq (.cv y) (synCop (.cv z) (.cv w)))
            (.classMem (synCop (.cv w) (.cv z)) (.cv x)))))
      z p0009
  have p0011 :=
    @gN3bitrri (synWrex x A (.classMem (.cv y) (synCcnv (.cv x))))
      (synWrex x A (synWex z (synWex w (synWa (.classEq (.cv y) (synCop (.cv z) (.cv w)))
              (.classMem (synCop (.cv w) (.cv z)) (.cv x))))))
      (synWex z (synWrex x A (synWex w (synWa (.classEq (.cv y) (synCop (.cv z) (.cv w)))
              (.classMem (synCop (.cv w) (.cv z)) (.cv x))))))
      (synWex z (synWex w (synWrex x A (synWa (.classEq (.cv y) (synCop (.cv z) (.cv w)))
              (.classMem (synCop (.cv w) (.cv z)) (.cv x))))))
      p0007 p0008 p0010
  have p0012 :=
    @gN3bitri (.classMem (.cv y) (synCcnv (synCuni A)))
      (synWex z (synWex w (synWa (.classEq (.cv y) (synCop (.cv z) (.cv w)))
            (.classMem (synCop (.cv w) (.cv z)) (synCuni A)))))
      (synWex z (synWex w (synWrex x A (synWa (.classEq (.cv y) (synCop (.cv z) (.cv w)))
              (.classMem (synCop (.cv w) (.cv z)) (.cv x))))))
      (synWrex x A (.classMem (.cv y) (synCcnv (.cv x)))) p0000 p0005 p0011
  have p0013 := @gEliun x (.cv y) A (synCcnv (.cv x)) dv_cache_0015
  have p0014 :=
    @gBitr4i (.classMem (.cv y) (synCcnv (synCuni A)))
      (synWrex x A (.classMem (.cv y) (synCcnv (.cv x))))
      (.classMem (.cv y) (synCiun x A (synCcnv (.cv x)))) p0012 p0013
  have p0015 :=
    @gEqriv y (synCcnv (synCuni A)) (synCiun x A (synCcnv (.cv x))) dv_cache_0016
      dv_cache_0017 p0014
  exact p0015

/-- Checked nominal proof certificate identified upstream as `g_elrn`. -/
@[expose]
noncomputable def gElrn (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf (synWb (.classMem A (synCrn B)) (synWex x (synWbr (.cv x) B A))) :=
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
  have dv_cache_0003 : x ∉ ((synCvv)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have p0000 := (Nominal.classEqRefl (synCrn B))
  have p0001 := @gEleq2i (synCrn B) (synCima B (synCvv)) A p0000
  have p0002 := @gElima x A B (synCvv) dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0003 := @gRexv (synWbr (.cv x) B A) x
  have p0004 :=
    @gN3bitri (.classMem A (synCrn B)) (.classMem A (synCima B (synCvv)))
      (synWrex x (synCvv) (synWbr (.cv x) B A)) (synWex x (synWbr (.cv x) B A)) p0001
      p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_elrn2`. -/
@[expose]
noncomputable def gElrn2 (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf
      (synWb (.classMem A (synCrn B)) (synWex x (.classMem (synCop (.cv x) A) B))) :=
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
  have p0000 := @gElrn x A B dv_cache_0001 dv_cache_0002
  have p0001 := (Nominal.biimpRefl (synWbr (.cv x) B A))
  have p0002 := @gExbii (synWbr (.cv x) B A) (.classMem (synCop (.cv x) A) B) x p0001
  have p0003 :=
    @gBitri (.classMem A (synCrn B)) (synWex x (synWbr (.cv x) B A))
      (synWex x (.classMem (synCop (.cv x) A) B)) p0000 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_eldm`. -/
@[expose]
noncomputable def gEldm (y : Var) (A : Class) (B : Class) (dv_A_y : y ∉ A.fv)
    (dv_B_y : y ∉ B.fv) :
    Nominal.NPrf (synWb (.classMem A (synCdm B)) (synWex y (synWbr A B (.cv y)))) :=
  by
  have dv_cache_0001 : y ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_y, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((synCcnv B)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, dv_B_y,
          not_false_eq_true])
  have p0000 := (Nominal.classEqRefl (synCdm B))
  have p0001 := @gEleq2i (synCdm B) (synCrn (synCcnv B)) A p0000
  have p0002 := @gElrn y A (synCcnv B) dv_cache_0001 dv_cache_0002
  have p0003 :=
    @gBitri (.classMem A (synCdm B)) (.classMem A (synCrn (synCcnv B)))
      (synWex y (synWbr (.cv y) (synCcnv B) A)) p0001 p0002
  have p0004 := @gBrcnv (.cv y) A B
  have p0005 := @gExbii (synWbr (.cv y) (synCcnv B) A) (synWbr A B (.cv y)) y p0004
  have p0006 :=
    @gBitri (.classMem A (synCdm B)) (synWex y (synWbr (.cv y) (synCcnv B) A))
      (synWex y (synWbr A B (.cv y))) p0003 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_eldm2`. -/
@[expose]
noncomputable def gEldm2 (y : Var) (A : Class) (B : Class) (dv_A_y : y ∉ A.fv)
    (dv_B_y : y ∉ B.fv) :
    Nominal.NPrf
      (synWb (.classMem A (synCdm B)) (synWex y (.classMem (synCop A (.cv y)) B))) :=
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
  have p0000 := @gEldm y A B dv_cache_0001 dv_cache_0002
  have p0001 := (Nominal.biimpRefl (synWbr A B (.cv y)))
  have p0002 := @gExbii (synWbr A B (.cv y)) (.classMem (synCop A (.cv y)) B) y p0001
  have p0003 :=
    @gBitri (.classMem A (synCdm B)) (synWex y (synWbr A B (.cv y)))
      (synWex y (.classMem (synCop A (.cv y)) B)) p0000 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_dfdm2`. -/
@[expose]
noncomputable def gDfdm2 (x : Var) (y : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.classEq (synCdm A) (.cab x (synWex y (synWbr (.cv x) A (.cv y))))) :=
  by
  have dv_cache_0001 : y ∉ ((Class.cv x)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          (Ne.symm dv_x_y), not_false_eq_true])
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
  have dv_cache_0003 : x ∉ ((synCdm A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, dv_A_x,
          not_false_eq_true])
  have p0000 := @gEldm y (.cv x) A dv_cache_0001 dv_cache_0002
  have p0001 :=
    @gEqabi (synWex y (synWbr (.cv x) A (.cv y))) x (synCdm A) dv_cache_0003 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_dfdm3`. -/
@[expose]
noncomputable def gDfdm3 (x : Var) (y : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.classEq (synCdm A) (.cab x (synWex y (.classMem (synCop (.cv x) (.cv y)) A)))) :=
  by
  have dv_cache_0001 : y ∉ ((Class.cv x)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          (Ne.symm dv_x_y), not_false_eq_true])
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
  have dv_cache_0003 : x ∉ ((synCdm A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, dv_A_x,
          not_false_eq_true])
  have p0000 := @gEldm2 y (.cv x) A dv_cache_0001 dv_cache_0002
  have p0001 :=
    @gEqabi (synWex y (.classMem (synCop (.cv x) (.cv y)) A)) x (synCdm A)
      dv_cache_0003 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_dfrn2`. -/
@[expose]
noncomputable def gDfrn2 (x : Var) (y : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.classEq (synCrn A) (.cab y (synWex x (synWbr (.cv x) A (.cv y))))) :=
  by
  have dv_cache_0001 : x ∉ ((Class.cv y)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, dv_x_y,
          not_false_eq_true])
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
  have dv_cache_0003 : y ∉ ((synCrn A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, dv_A_y,
          not_false_eq_true])
  have p0000 := @gElrn x (.cv y) A dv_cache_0001 dv_cache_0002
  have p0001 :=
    @gEqabi (synWex x (synWbr (.cv x) A (.cv y))) y (synCrn A) dv_cache_0003 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_dfrn3`. -/
@[expose]
noncomputable def gDfrn3 (x : Var) (y : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.classEq (synCrn A) (.cab y (synWex x (.classMem (synCop (.cv x) (.cv y)) A)))) :=
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
  have p0000 := @gDfrn2 x y A dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 := (Nominal.biimpRefl (synWbr (.cv x) A (.cv y)))
  have p0002 :=
    @gExbii (synWbr (.cv x) A (.cv y)) (.classMem (synCop (.cv x) (.cv y)) A) x p0001
  have p0003 :=
    @gAbbii (synWex x (synWbr (.cv x) A (.cv y)))
      (synWex x (.classMem (synCop (.cv x) (.cv y)) A)) y p0002
  have p0004 :=
    @gEqtri (synCrn A) (.cab y (synWex x (synWbr (.cv x) A (.cv y))))
      (.cab y (synWex x (.classMem (synCop (.cv x) (.cv y)) A))) p0000 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_dfrn4`. -/
@[expose]
noncomputable def gDfrn4 (A : Class) :
    Nominal.NPrf (.classEq (synCrn A) (synCdm (synCcnv A))) :=
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
  have dv_cache_0001 : y ∉ ((Class.cv x)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_x, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((synCcnv A)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, fresh_y_not_A,
          not_false_eq_true])
  have dv_cache_0003 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((synCrn A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, fresh_x_not_A,
          not_false_eq_true])
  have dv_cache_0005 : x ∉ ((synCdm (synCcnv A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, fresh_x_not_A,
          not_false_eq_true])
  have p0000 := @gBrcnv (.cv x) (.cv y) A
  have p0001 :=
    @gExbii (synWbr (.cv x) (synCcnv A) (.cv y)) (synWbr (.cv y) A (.cv x)) y p0000
  have p0002 := @gEldm y (.cv x) (synCcnv A) dv_cache_0001 dv_cache_0002
  have p0003 := @gElrn y (.cv x) A dv_cache_0001 dv_cache_0003
  have p0004 :=
    @gN3bitr4ri (synWex y (synWbr (.cv x) (synCcnv A) (.cv y)))
      (synWex y (synWbr (.cv y) A (.cv x))) (.classMem (.cv x) (synCdm (synCcnv A)))
      (.classMem (.cv x) (synCrn A)) p0001 p0002 p0003
  have p0005 :=
    @gEqriv x (synCrn A) (synCdm (synCcnv A)) dv_cache_0004 dv_cache_0005 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_dfdmf`. -/
@[expose]
noncomputable def gDfdmf (x : Var) (y : Var) (A : Class) (dv_x_y : x ≠ y)
    (hyp_dfdmf_1 : Nominal.NPrf (synWnfc x A))
    (hyp_dfdmf_2 : Nominal.NPrf (synWnfc y A)) :
    Nominal.NPrf
      (.classEq (synCdm A) (.cab x (synWex y (synWbr (.cv x) A (.cv y))))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv
  let w : Var := freshVar proofSupport 0
  let v : Var := freshVar proofSupport 1
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
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
  have fresh_v : v ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_v_ne_y : v ≠ y := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_y_ne_v : y ≠ v := Ne.symm fresh_v_ne_y
  have fresh_v_not_A : v ∉ A.fv := by
    intro h
    exact fresh_v (Finset.mem_union_right _ (h))
  have fresh_w_ne_v : w ≠ v :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_v_ne_w : v ≠ w := Ne.symm fresh_w_ne_v
  have dv_cache_0001 : w ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_A, not_false_eq_true])
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
  have dv_cache_0003 : w ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show w ≠ v from (by exact fresh_w_ne_v))
  have dv_cache_0004 : y ∉ ((Class.cv w)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_w, not_false_eq_true])
  have dv_cache_0005 : y ∉ ((Class.cv v)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_v, not_false_eq_true])
  have dv_cache_0006 : v ∉ ((synWbr (.cv w) A (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_v_ne_w, fresh_v_ne_y, fresh_v_not_A, or_false,
          not_false_eq_true])
  have dv_cache_0007 : x ∉ ((Class.cv w)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_w, not_false_eq_true])
  have dv_cache_0008 : x ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, dv_x_y,
          not_false_eq_true])
  have dv_cache_0009 : w ∉ ((synWex y (synWbr (.cv x) A (.cv y)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_w_ne_x, fresh_w_ne_y, fresh_w_not_A, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0010 : y ∉ ((Wff.objEq w x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
          Finset.mem_singleton, fresh_y_ne_w, (Ne.symm dv_x_y), or_false,
          not_false_eq_true])
  have p0000 := @gDfdm2 w v A dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 := @gNfcv y (.cv w) dv_cache_0004
  have p0002 := @gNfcv y (.cv v) dv_cache_0005
  have p0003 := @gNfbr y (.cv w) (.cv v) A p0001 hyp_dfdmf_2 p0002
  have p0004 := @gNfv (synWbr (.cv w) A (.cv y)) v dv_cache_0006
  have p0005 := @gBreq2 (.cv v) (.cv y) (.cv w) A
  have p0006_e02_recanon :
    Nominal.NPrf
      (.imp (.objEq v y) (synWb (synWbr (.cv w) A (.cv v)) (synWbr (.cv w) A (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWbr synCop synCun synCnin synWnan synWa synCcompl synWrex
          synWex synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0005
  have p0006 :=
    @gCbvex (synWbr (.cv w) A (.cv v)) (synWbr (.cv w) A (.cv y)) v y p0003 p0004
      p0006_e02_recanon
  have p0007 :=
    @gAbbii (synWex v (synWbr (.cv w) A (.cv v)))
      (synWex y (synWbr (.cv w) A (.cv y))) w p0006
  have p0008 := @gNfcv x (.cv w) dv_cache_0007
  have p0009 := @gNfcv x (.cv y) dv_cache_0008
  have p0010 := @gNfbr x (.cv w) (.cv y) A p0008 hyp_dfdmf_1 p0009
  have p0011 := @gNfex (synWbr (.cv w) A (.cv y)) x y p0010
  have p0012 := @gNfv (synWex y (synWbr (.cv x) A (.cv y))) w dv_cache_0009
  have p0013 := @gBreq1 (.cv w) (.cv x) (.cv y) A
  have p0014_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq w x) (synWb (synWbr (.cv w) A (.cv y)) (synWbr (.cv x) A (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWbr synCop synCun synCnin synWnan synWa synCcompl synWrex
          synWex synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0013
  have p0014 :=
    @gExbidv (.objEq w x) (synWbr (.cv w) A (.cv y)) (synWbr (.cv x) A (.cv y)) y
      dv_cache_0010 p0014_e00_recanon
  have p0015 :=
    @gCbvab (synWex y (synWbr (.cv w) A (.cv y)))
      (synWex y (synWbr (.cv x) A (.cv y))) w x p0011 p0012 p0014
  have p0016 :=
    @gN3eqtri (synCdm A) (.cab w (synWex v (synWbr (.cv w) A (.cv v))))
      (.cab w (synWex y (synWbr (.cv w) A (.cv y))))
      (.cab x (synWex y (synWbr (.cv x) A (.cv y)))) p0000 p0007 p0015
  exact p0016

/-- Checked nominal proof certificate identified upstream as `g_dmss`. -/
@[expose]
noncomputable def gDmss (A : Class) (B : Class) :
    Nominal.NPrf (.imp (synWss A B) (synWss (synCdm A) (synCdm B))) :=
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
  have dv_cache_0001 : y ∉ ((synWss A B)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union,
          fresh_y_not_A, fresh_y_not_B, or_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_x, not_false_eq_true])
  have dv_cache_0003 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
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
  have dv_cache_0005 : x ∉ ((synCdm A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, fresh_x_not_A,
          not_false_eq_true])
  have dv_cache_0006 : x ∉ ((synCdm B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, fresh_x_not_B,
          not_false_eq_true])
  have dv_cache_0007 : x ∉ ((synWss A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true])
  have p0000 := @gSsel A B (synCop (.cv x) (.cv y))
  have p0001 :=
    @gEximdv (synWss A B) (.classMem (synCop (.cv x) (.cv y)) A)
      (.classMem (synCop (.cv x) (.cv y)) B) y dv_cache_0001 p0000
  have p0002 := @gEldm2 y (.cv x) A dv_cache_0002 dv_cache_0003
  have p0003 := @gEldm2 y (.cv x) B dv_cache_0002 dv_cache_0004
  have p0004 :=
    @gN3imtr4g (synWss A B) (synWex y (.classMem (synCop (.cv x) (.cv y)) A))
      (synWex y (.classMem (synCop (.cv x) (.cv y)) B)) (.classMem (.cv x) (synCdm A))
      (.classMem (.cv x) (synCdm B)) p0001 p0002 p0003
  have p0005 :=
    @gSsrdv (synWss A B) x (synCdm A) (synCdm B) dv_cache_0005 dv_cache_0006
      dv_cache_0007 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_dmeq`. -/
@[expose]
noncomputable def gDmeq (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (synCdm A) (synCdm B))) :=
  by
  have p0000 := @gDmss A B
  have p0001 := @gDmss B A
  have p0002 :=
    @gAnim12i (synWss A B) (synWss (synCdm A) (synCdm B)) (synWss B A)
      (synWss (synCdm B) (synCdm A)) p0000 p0001
  have p0003 := @gEqss A B
  have p0004 := @gEqss (synCdm A) (synCdm B)
  have p0005 :=
    @gN3imtr4i (synWa (synWss A B) (synWss B A))
      (synWa (synWss (synCdm A) (synCdm B)) (synWss (synCdm B) (synCdm A)))
      (.classEq A B) (.classEq (synCdm A) (synCdm B)) p0002 p0003 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_dmeqi`. -/
@[expose]
noncomputable def gDmeqi (A : Class) (B : Class)
    (hyp_dmeqi_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (.classEq (synCdm A) (synCdm B)) :=
  by
  have p0000 := @gDmeq A B
  have p0001 := Nominal.mp hyp_dmeqi_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_dmeqd`. -/
@[expose]
noncomputable def gDmeqd (ph : Wff) (A : Class) (B : Class)
    (hyp_dmeqd_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (synCdm A) (synCdm B))) :=
  by
  have p0000 := @gDmeq A B
  have p0001 :=
    @gSyl ph (.classEq A B) (.classEq (synCdm A) (synCdm B)) hyp_dmeqd_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_opeldm`. -/
@[expose]
noncomputable def gOpeldm (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classMem (synCop A B) C) (.classMem A (synCdm C))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have dv_cache_0001 : y ∉ (B).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_B, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((Wff.classMem (synCop A B) C)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          fresh_y_not_A, fresh_y_not_B, fresh_y_not_C, or_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
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
  have p0000 := @gElex (synCop A B) C
  have p0001 := @gOpexb A B
  have p0002 :=
    @gSimprbi (.classMem (synCop A B) (synCvv)) (.classMem A (synCvv))
      (.classMem B (synCvv)) p0001
  have p0003 :=
    @gSyl (.classMem (synCop A B) C) (.classMem (synCop A B) (synCvv))
      (.classMem B (synCvv)) p0000 p0002
  have p0004 := @gOpeq2 (.cv y) B A
  have p0005 := @gEleq1d (.classEq (.cv y) B) (synCop A (.cv y)) (synCop A B) C p0004
  have p0006 :=
    @gSpcegv (.classMem (synCop A (.cv y)) C) (.classMem (synCop A B) C) y B (synCvv)
      dv_cache_0001 dv_cache_0002 p0005
  have p0007 :=
    @gMpcom (.classMem B (synCvv)) (.classMem (synCop A B) C)
      (synWex y (.classMem (synCop A (.cv y)) C)) p0003 p0006
  have p0008 := @gEldm2 y A C dv_cache_0003 dv_cache_0004
  have p0009 :=
    @gSylibr (.classMem (synCop A B) C) (synWex y (.classMem (synCop A (.cv y)) C))
      (.classMem A (synCdm C)) p0007 p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_breldm`. -/
@[expose]
noncomputable def gBreldm (A : Class) (B : Class) (R : Class) :
    Nominal.NPrf (.imp (synWbr A R B) (.classMem A (synCdm R))) :=
  by
  have p0000 := (Nominal.biimpRefl (synWbr A R B))
  have p0001 := @gOpeldm A B R
  have p0002 :=
    @gSylbi (synWbr A R B) (.classMem (synCop A B) R) (.classMem A (synCdm R)) p0000
      p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_dmun`. -/
@[expose]
noncomputable def gDmun (A : Class) (B : Class) :
    Nominal.NPrf (.classEq (synCdm (synCun A B)) (synCun (synCdm A) (synCdm B))) :=
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
  have dv_cache_0001 : x ∉ ((synCun A B)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((synCun A B)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
          fresh_y_not_A, fresh_y_not_B, or_false, not_false_eq_true])
  have dv_cache_0003 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show x ≠ y from (by exact fresh_x_ne_y))
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
  have dv_cache_0007 : x ∉ ((synCun (synCdm A) (synCdm B))).fv :=
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true])
  have p0000 := @gDfdm3 x y (synCun A B) dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 := @gEldm y (.cv x) A dv_cache_0004 dv_cache_0005
  have p0002 := @gEldm y (.cv x) B dv_cache_0004 dv_cache_0006
  have p0003 :=
    @gOrbi12i (.classMem (.cv x) (synCdm A)) (synWex y (synWbr (.cv x) A (.cv y)))
      (.classMem (.cv x) (synCdm B)) (synWex y (synWbr (.cv x) B (.cv y))) p0001 p0002
  have p0004 := @gElun (.cv x) (synCdm A) (synCdm B)
  have p0005 := (Nominal.biimpRefl (synWbr (.cv x) (synCun A B) (.cv y)))
  have p0006 := @gBrun (.cv x) (.cv y) A B
  have p0007 :=
    @gBitr3i (.classMem (synCop (.cv x) (.cv y)) (synCun A B))
      (synWbr (.cv x) (synCun A B) (.cv y))
      (synWo (synWbr (.cv x) A (.cv y)) (synWbr (.cv x) B (.cv y))) p0005 p0006
  have p0008 :=
    @gExbii (.classMem (synCop (.cv x) (.cv y)) (synCun A B))
      (synWo (synWbr (.cv x) A (.cv y)) (synWbr (.cv x) B (.cv y))) y p0007
  have p0009 := @gN1943 (synWbr (.cv x) A (.cv y)) (synWbr (.cv x) B (.cv y)) y
  have p0010 :=
    @gBitri (synWex y (.classMem (synCop (.cv x) (.cv y)) (synCun A B)))
      (synWex y (synWo (synWbr (.cv x) A (.cv y)) (synWbr (.cv x) B (.cv y))))
      (synWo (synWex y (synWbr (.cv x) A (.cv y))) (synWex y (synWbr (.cv x) B (.cv y))))
      p0008 p0009
  have p0011 :=
    @gN3bitr4i (synWo (.classMem (.cv x) (synCdm A)) (.classMem (.cv x) (synCdm B)))
      (synWo (synWex y (synWbr (.cv x) A (.cv y))) (synWex y (synWbr (.cv x) B (.cv y))))
      (.classMem (.cv x) (synCun (synCdm A) (synCdm B)))
      (synWex y (.classMem (synCop (.cv x) (.cv y)) (synCun A B))) p0003 p0004 p0010
  have p0012 :=
    @gEqabi (synWex y (.classMem (synCop (.cv x) (.cv y)) (synCun A B))) x
      (synCun (synCdm A) (synCdm B)) dv_cache_0007 p0011
  have p0013 :=
    @gEqtr4i (synCdm (synCun A B))
      (.cab x (synWex y (.classMem (synCop (.cv x) (.cv y)) (synCun A B))))
      (synCun (synCdm A) (synCdm B)) p0000 p0012
  exact p0013


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk011Compact001Part003`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_dmuni`. -/
@[expose]
noncomputable def gDmuni (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (.classEq (synCdm (synCuni A)) (synCiun x A (synCdm (.cv x)))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv
  let y : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
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
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_z_ne_y : z ≠ y := Ne.symm fresh_y_ne_z
  have dv_cache_0001 : x ∉ ((synCop (.cv y) (.cv z))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_y, fresh_x_ne_z, or_false, not_false_eq_true])
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
  have dv_cache_0003 : z ∉ ((Wff.classMem (.cv x) A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_x, fresh_z_not_A, or_false, not_false_eq_true])
  have dv_cache_0004 : z ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_y, not_false_eq_true])
  have dv_cache_0005 : z ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_x, not_false_eq_true])
  have dv_cache_0006 : z ∉ ((synCuni A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, fresh_z_not_A,
          not_false_eq_true])
  have dv_cache_0007 : x ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_y, not_false_eq_true])
  have dv_cache_0008 : y ∉ ((synCdm (synCuni A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, fresh_y_not_A,
          not_false_eq_true])
  have dv_cache_0009 : y ∉ ((synCiun x A (synCdm (.cv x)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ciun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_y_not_A, fresh_y_ne_x, or_false, and_false,
          not_false_eq_true])
  have p0000 := @gEluni x (synCop (.cv y) (.cv z)) A dv_cache_0001 dv_cache_0002
  have p0001 :=
    @gExbii (.classMem (synCop (.cv y) (.cv z)) (synCuni A))
      (synWex x (synWa (.classMem (synCop (.cv y) (.cv z)) (.cv x)) (.classMem (.cv x) A)))
      z p0000
  have p0002 :=
    @gExcom (synWa (.classMem (synCop (.cv y) (.cv z)) (.cv x)) (.classMem (.cv x) A))
      z x
  have p0003 :=
    @gN1941v (.classMem (synCop (.cv y) (.cv z)) (.cv x)) (.classMem (.cv x) A) z
      dv_cache_0003
  have p0004 := @gAncom (.classMem (.cv x) A) (.classMem (.cv y) (synCdm (.cv x)))
  have p0005 := @gEldm2 z (.cv y) (.cv x) dv_cache_0004 dv_cache_0005
  have p0006 :=
    @gAnbi1i (.classMem (.cv y) (synCdm (.cv x)))
      (synWex z (.classMem (synCop (.cv y) (.cv z)) (.cv x))) (.classMem (.cv x) A)
      p0005
  have p0007 :=
    @gBitri (synWa (.classMem (.cv x) A) (.classMem (.cv y) (synCdm (.cv x))))
      (synWa (.classMem (.cv y) (synCdm (.cv x))) (.classMem (.cv x) A))
      (synWa (synWex z (.classMem (synCop (.cv y) (.cv z)) (.cv x))) (.classMem (.cv x) A))
      p0004 p0006
  have p0008 :=
    @gBicomi (synWa (.classMem (.cv x) A) (.classMem (.cv y) (synCdm (.cv x))))
      (synWa (synWex z (.classMem (synCop (.cv y) (.cv z)) (.cv x))) (.classMem (.cv x) A))
      p0007
  have p0009 :=
    @gBitri
      (synWex z (synWa (.classMem (synCop (.cv y) (.cv z)) (.cv x)) (.classMem (.cv x) A)))
      (synWa (synWex z (.classMem (synCop (.cv y) (.cv z)) (.cv x))) (.classMem (.cv x) A))
      (synWa (.classMem (.cv x) A) (.classMem (.cv y) (synCdm (.cv x)))) p0003 p0008
  have p0010 :=
    @gExbii
      (synWex z (synWa (.classMem (synCop (.cv y) (.cv z)) (.cv x)) (.classMem (.cv x) A)))
      (synWa (.classMem (.cv x) A) (.classMem (.cv y) (synCdm (.cv x)))) x p0009
  have p0011 :=
    @gN3bitri (synWex z (.classMem (synCop (.cv y) (.cv z)) (synCuni A)))
      (synWex z (synWex x
          (synWa (.classMem (synCop (.cv y) (.cv z)) (.cv x)) (.classMem (.cv x) A))))
      (synWex x (synWex z
          (synWa (.classMem (synCop (.cv y) (.cv z)) (.cv x)) (.classMem (.cv x) A))))
      (synWex x (synWa (.classMem (.cv x) A) (.classMem (.cv y) (synCdm (.cv x)))))
      p0001 p0002 p0010
  have p0012 := (Nominal.biimpRefl (synWrex x A (.classMem (.cv y) (synCdm (.cv x)))))
  have p0013 :=
    @gBitr4i (synWex z (.classMem (synCop (.cv y) (.cv z)) (synCuni A)))
      (synWex x (synWa (.classMem (.cv x) A) (.classMem (.cv y) (synCdm (.cv x)))))
      (synWrex x A (.classMem (.cv y) (synCdm (.cv x)))) p0011 p0012
  have p0014 := @gEldm2 z (.cv y) (synCuni A) dv_cache_0004 dv_cache_0006
  have p0015 := @gEliun x (.cv y) A (synCdm (.cv x)) dv_cache_0007
  have p0016 :=
    @gN3bitr4i (synWex z (.classMem (synCop (.cv y) (.cv z)) (synCuni A)))
      (synWrex x A (.classMem (.cv y) (synCdm (.cv x))))
      (.classMem (.cv y) (synCdm (synCuni A)))
      (.classMem (.cv y) (synCiun x A (synCdm (.cv x)))) p0013 p0014 p0015
  have p0017 :=
    @gEqriv y (synCdm (synCuni A)) (synCiun x A (synCdm (.cv x))) dv_cache_0008
      dv_cache_0009 p0016
  exact p0017

/-- Checked nominal proof certificate identified upstream as `g_dmopab`. -/
@[expose]
noncomputable def gDmopab (ph : Wff) (x : Var) (y : Var) (dv_x_y : x ≠ y) :
    Nominal.NPrf (.classEq (synCdm (synCopab x y ph)) (.cab x (synWex y ph))) :=
  by
  have dv_cache_0001 : x ≠ y := by exact (show x ≠ y from (by exact dv_x_y))
  have p0000 := @gNfopab1 ph x y
  have p0001 := @gNfopab2 ph x y
  have p0002 := @gDfdmf x y (synCopab x y ph) dv_cache_0001 p0000 p0001
  have p0003 := (Nominal.biimpRefl (synWbr (.cv x) (synCopab x y ph) (.cv y)))
  have p0004 := @gOpabid ph x y
  have p0005 :=
    @gBitri (synWbr (.cv x) (synCopab x y ph) (.cv y))
      (.classMem (synCop (.cv x) (.cv y)) (synCopab x y ph)) ph p0003 p0004
  have p0006 := @gExbii (synWbr (.cv x) (synCopab x y ph) (.cv y)) ph y p0005
  have p0007 :=
    @gAbbii (synWex y (synWbr (.cv x) (synCopab x y ph) (.cv y))) (synWex y ph) x
      p0006
  have p0008 :=
    @gEqtri (synCdm (synCopab x y ph))
      (.cab x (synWex y (synWbr (.cv x) (synCopab x y ph) (.cv y))))
      (.cab x (synWex y ph)) p0002 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_dmopab3`. -/
@[expose]
noncomputable def gDmopab3 (ph : Wff) (x : Var) (y : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (synWb (synWral x A (synWex y ph))
        (.classEq (synCdm (synCopab x y (synWa (.classMem (.cv x) A) ph))) A)) :=
  by
  have dv_cache_0001 : x ≠ y := by exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0002 : y ∉ ((Wff.classMem (.cv x) A)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_x_y), dv_A_y, or_false, not_false_eq_true])
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
  have p0000 := (Nominal.biimpRefl (synWral x A (synWex y ph)))
  have p0001 := @gPm471 (.classMem (.cv x) A) (synWex y ph)
  have p0002 :=
    @gAlbii (.imp (.classMem (.cv x) A) (synWex y ph))
      (synWb (.classMem (.cv x) A) (synWa (.classMem (.cv x) A) (synWex y ph))) x p0001
  have p0003 := @gDmopab (synWa (.classMem (.cv x) A) ph) x y dv_cache_0001
  have p0004 := @gN1942v (.classMem (.cv x) A) ph y dv_cache_0002
  have p0005 :=
    @gAbbii (synWex y (synWa (.classMem (.cv x) A) ph))
      (synWa (.classMem (.cv x) A) (synWex y ph)) x p0004
  have p0006 :=
    @gEqtri (synCdm (synCopab x y (synWa (.classMem (.cv x) A) ph)))
      (.cab x (synWex y (synWa (.classMem (.cv x) A) ph)))
      (.cab x (synWa (.classMem (.cv x) A) (synWex y ph))) p0003 p0005
  have p0007 :=
    @gEqeq1i (synCdm (synCopab x y (synWa (.classMem (.cv x) A) ph)))
      (.cab x (synWa (.classMem (.cv x) A) (synWex y ph))) A p0006
  have p0008 := @gEqcom A (.cab x (synWa (.classMem (.cv x) A) (synWex y ph)))
  have p0009 := @gEqabb (synWa (.classMem (.cv x) A) (synWex y ph)) x A dv_cache_0003
  have p0010 :=
    @gN3bitr2ri (.classEq (synCdm (synCopab x y (synWa (.classMem (.cv x) A) ph))) A)
      (.classEq (.cab x (synWa (.classMem (.cv x) A) (synWex y ph))) A)
      (.classEq A (.cab x (synWa (.classMem (.cv x) A) (synWex y ph))))
      (.all x (synWb (.classMem (.cv x) A) (synWa (.classMem (.cv x) A) (synWex y ph))))
      p0007 p0008 p0009
  have p0011 :=
    @gN3bitri (synWral x A (synWex y ph))
      (.all x (.imp (.classMem (.cv x) A) (synWex y ph)))
      (.all x (synWb (.classMem (.cv x) A) (synWa (.classMem (.cv x) A) (synWex y ph))))
      (.classEq (synCdm (synCopab x y (synWa (.classMem (.cv x) A) ph))) A) p0000 p0002
      p0010
  exact p0011

/-- Checked nominal proof certificate identified upstream as `g_dm0`. -/
@[expose]
noncomputable def gDm0 : Nominal.NPrf (.classEq (synCdm (synC0)) (synC0)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have dv_cache_0001 : x ∉ ((synCdm (synC0))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, compact_fv_not_mem_empty,
          not_false_eq_true])
  have dv_cache_0002 : y ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_x, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((synC0)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          compact_fv_not_mem_empty, not_false_eq_true])
  have p0000 := @gEq0 x (synCdm (synC0)) dv_cache_0001
  have p0001 := @gNoel (synCop (.cv x) (.cv y))
  have p0002 := @gNex (.classMem (synCop (.cv x) (.cv y)) (synC0)) y p0001
  have p0003 := @gEldm2 y (.cv x) (synC0) dv_cache_0002 dv_cache_0003
  have p0004 :=
    @gMtbir (.classMem (.cv x) (synCdm (synC0)))
      (synWex y (.classMem (synCop (.cv x) (.cv y)) (synC0))) p0002 p0003
  have p0005 :=
    @gMpgbir (.classEq (synCdm (synC0)) (synC0))
      (.neg (.classMem (.cv x) (synCdm (synC0)))) x p0000 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_dmi`. -/
@[expose]
noncomputable def gDmi : Nominal.NPrf (.classEq (synCdm (synCid)) (synCvv)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have dv_cache_0001 : x ∉ ((synCdm (synCid))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, compact_fv_not_mem_empty,
          not_false_eq_true])
  have dv_cache_0002 : y ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_x, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((synCid)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          compact_fv_not_mem_empty, not_false_eq_true])
  have p0000 := @gEqv x (synCdm (synCid)) dv_cache_0001
  have p0001 := @gA9e y x
  have p0002 := @gVex y
  have p0003 := @gIdeq (.cv x) (.cv y) p0002
  have p0004 := @gEqucom x y
  have p0005_e00_recanon :
    Nominal.NPrf (synWb (synWbr (.cv x) (synCid) (.cv y)) (.objEq x y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWbr synCop synCun synCnin synWnan synWa synCcompl synWrex
          synWex synCphi synCid synCopab
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0003
  have p0005 :=
    @gBitri (synWbr (.cv x) (synCid) (.cv y)) (.objEq x y) (.objEq y x)
      p0005_e00_recanon p0004
  have p0006 := @gExbii (synWbr (.cv x) (synCid) (.cv y)) (.objEq y x) y p0005
  have p0007 :=
    @gMpbir (synWex y (synWbr (.cv x) (synCid) (.cv y))) (synWex y (.objEq y x))
      p0001 p0006
  have p0008 := @gEldm y (.cv x) (synCid) dv_cache_0002 dv_cache_0003
  have p0009 :=
    @gMpbir (.classMem (.cv x) (synCdm (synCid)))
      (synWex y (synWbr (.cv x) (synCid) (.cv y))) p0007 p0008
  have p0010 :=
    @gMpgbir (.classEq (synCdm (synCid)) (synCvv))
      (.classMem (.cv x) (synCdm (synCid))) x p0000 p0009
  exact p0010

/-- Checked nominal proof certificate identified upstream as `g_dm0rn0`. -/
@[expose]
noncomputable def gDm0rn0 (A : Class) :
    Nominal.NPrf
      (synWb (.classEq (synCdm A) (synC0)) (.classEq (synCrn A) (synC0))) :=
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
  have dv_cache_0001 : x ∉ ((synC0)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((synC0)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0003 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
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
  have p0000 := @gAlnex (synWex y (synWbr (.cv x) A (.cv y))) x
  have p0001 := @gExcom (synWbr (.cv x) A (.cv y)) x y
  have p0002 :=
    @gXchbinx (.all x (.neg (synWex y (synWbr (.cv x) A (.cv y)))))
      (synWex x (synWex y (synWbr (.cv x) A (.cv y))))
      (synWex y (synWex x (synWbr (.cv x) A (.cv y)))) p0000 p0001
  have p0003 := @gAlnex (synWex x (synWbr (.cv x) A (.cv y))) y
  have p0004 :=
    @gBitr4i (.all x (.neg (synWex y (synWbr (.cv x) A (.cv y)))))
      (.neg (synWex y (synWex x (synWbr (.cv x) A (.cv y)))))
      (.all y (.neg (synWex x (synWbr (.cv x) A (.cv y))))) p0002 p0003
  have p0005 := @gNoel (.cv x)
  have p0006 :=
    @gNbn (.classMem (.cv x) (synC0)) (synWex y (synWbr (.cv x) A (.cv y))) p0005
  have p0007 :=
    @gAlbii (.neg (synWex y (synWbr (.cv x) A (.cv y))))
      (synWb (synWex y (synWbr (.cv x) A (.cv y))) (.classMem (.cv x) (synC0))) x
      p0006
  have p0008 := @gNoel (.cv y)
  have p0009 :=
    @gNbn (.classMem (.cv y) (synC0)) (synWex x (synWbr (.cv x) A (.cv y))) p0008
  have p0010 :=
    @gAlbii (.neg (synWex x (synWbr (.cv x) A (.cv y))))
      (synWb (synWex x (synWbr (.cv x) A (.cv y))) (.classMem (.cv y) (synC0))) y
      p0009
  have p0011 :=
    @gN3bitr3i (.all x (.neg (synWex y (synWbr (.cv x) A (.cv y)))))
      (.all y (.neg (synWex x (synWbr (.cv x) A (.cv y)))))
      (.all x (synWb (synWex y (synWbr (.cv x) A (.cv y))) (.classMem (.cv x) (synC0))))
      (.all y (synWb (synWex x (synWbr (.cv x) A (.cv y))) (.classMem (.cv y) (synC0))))
      p0004 p0007 p0010
  have p0012 := @gEqabcb (synWex y (synWbr (.cv x) A (.cv y))) x (synC0) dv_cache_0001
  have p0013 := @gEqabcb (synWex x (synWbr (.cv x) A (.cv y))) y (synC0) dv_cache_0002
  have p0014 :=
    @gN3bitr4i
      (.all x (synWb (synWex y (synWbr (.cv x) A (.cv y))) (.classMem (.cv x) (synC0))))
      (.all y (synWb (synWex x (synWbr (.cv x) A (.cv y))) (.classMem (.cv y) (synC0))))
      (.classEq (.cab x (synWex y (synWbr (.cv x) A (.cv y)))) (synC0))
      (.classEq (.cab y (synWex x (synWbr (.cv x) A (.cv y)))) (synC0)) p0011 p0012
      p0013
  have p0015 := @gDfdm2 x y A dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0016 :=
    @gEqeq1i (synCdm A) (.cab x (synWex y (synWbr (.cv x) A (.cv y)))) (synC0) p0015
  have p0017 := @gDfrn2 x y A dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0018 :=
    @gEqeq1i (synCrn A) (.cab y (synWex x (synWbr (.cv x) A (.cv y)))) (synC0) p0017
  have p0019 :=
    @gN3bitr4i (.classEq (.cab x (synWex y (synWbr (.cv x) A (.cv y)))) (synC0))
      (.classEq (.cab y (synWex x (synWbr (.cv x) A (.cv y)))) (synC0))
      (.classEq (synCdm A) (synC0)) (.classEq (synCrn A) (synC0)) p0014 p0016 p0018
  exact p0019

/-- Checked nominal proof certificate identified upstream as `g_dmeq0`. -/
@[expose]
noncomputable def gDmeq0 (A : Class) :
    Nominal.NPrf (synWb (.classEq A (synC0)) (.classEq (synCdm A) (synC0))) :=
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
  have dv_cache_0001 : y ∉ ((Class.cv x)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_x, not_false_eq_true])
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
  have dv_cache_0003 : x ∉ ((synCdm A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, fresh_x_not_A,
          not_false_eq_true])
  have dv_cache_0004 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((synC0)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0006 : y ∉ ((synC0)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0007 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 := @gEldm2 y (.cv x) A dv_cache_0001 dv_cache_0002
  have p0001 :=
    @gNotbii (.classMem (.cv x) (synCdm A))
      (synWex y (.classMem (synCop (.cv x) (.cv y)) A)) p0000
  have p0002 := @gAlnex (.classMem (synCop (.cv x) (.cv y)) A) y
  have p0003 := @gNoel (synCop (.cv x) (.cv y))
  have p0004 :=
    @gNbn (.classMem (synCop (.cv x) (.cv y)) (synC0))
      (.classMem (synCop (.cv x) (.cv y)) A) p0003
  have p0005 :=
    @gAlbii (.neg (.classMem (synCop (.cv x) (.cv y)) A))
      (synWb (.classMem (synCop (.cv x) (.cv y)) A)
        (.classMem (synCop (.cv x) (.cv y)) (synC0)))
      y p0004
  have p0006 :=
    @gN3bitr2i (.neg (.classMem (.cv x) (synCdm A)))
      (.neg (synWex y (.classMem (synCop (.cv x) (.cv y)) A)))
      (.all y (.neg (.classMem (synCop (.cv x) (.cv y)) A)))
      (.all y (synWb (.classMem (synCop (.cv x) (.cv y)) A)
          (.classMem (synCop (.cv x) (.cv y)) (synC0))))
      p0001 p0002 p0005
  have p0007 :=
    @gAlbii (.neg (.classMem (.cv x) (synCdm A)))
      (.all y (synWb (.classMem (synCop (.cv x) (.cv y)) A)
          (.classMem (synCop (.cv x) (.cv y)) (synC0))))
      x p0006
  have p0008 := @gEq0 x (synCdm A) dv_cache_0003
  have p0009 :=
    @gEqrel x y A (synC0) dv_cache_0004 dv_cache_0002 dv_cache_0005 dv_cache_0006
      dv_cache_0007
  have p0010 :=
    @gN3bitr4ri (.all x (.neg (.classMem (.cv x) (synCdm A))))
      (.all x (.all y (synWb (.classMem (synCop (.cv x) (.cv y)) A)
            (.classMem (synCop (.cv x) (.cv y)) (synC0)))))
      (.classEq (synCdm A) (synC0)) (.classEq A (synC0)) p0007 p0008 p0009
  exact p0010

/-- Checked nominal proof certificate identified upstream as `g_dmxp`. -/
@[expose]
noncomputable def gDmxp (A : Class) (B : Class) :
    Nominal.NPrf (.imp (synWne B (synC0)) (.classEq (synCdm (synCxp A B)) A)) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let y : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y_ne_x : y ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : y ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0002 : x ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
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
        simp only [fresh_x_not_B, not_false_eq_true])
  have dv_cache_0005 : y ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show y ≠ x from (by exact fresh_y_ne_x))
  have dv_cache_0006 : y ∉ ((synWne B (synC0))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          fresh_y_not_B, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfXp y x A B
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0001 :=
    @gDmeqi (synCxp A B)
      (synCopab y x (synWa (.classMem (.cv y) A) (.classMem (.cv x) B))) p0000
  have p0002 := @gN0 x B dv_cache_0004
  have p0003 := @gBiimpi (synWne B (synC0)) (synWex x (.classMem (.cv x) B)) p0002
  have p0004 :=
    @gRalrimivw (synWne B (synC0)) (synWex x (.classMem (.cv x) B)) y A dv_cache_0006
      p0003
  have p0005 :=
    @gDmopab3 (.classMem (.cv x) B) y x A dv_cache_0001 dv_cache_0002 dv_cache_0005
  have p0006 :=
    @gSylib (synWne B (synC0)) (synWral y A (synWex x (.classMem (.cv x) B)))
      (.classEq
        (synCdm (synCopab y x (synWa (.classMem (.cv y) A) (.classMem (.cv x) B)))) A)
      p0004 p0005
  have p0007 :=
    @gSyl5eq (synWne B (synC0)) (synCdm (synCxp A B))
      (synCdm (synCopab y x (synWa (.classMem (.cv y) A) (.classMem (.cv x) B)))) A
      p0001 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_reseq1`. -/
@[expose]
noncomputable def gReseq1 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (synCres A C) (synCres B C))) :=
  by
  have p0000 := @gIneq1 A B (synCxp C (synCvv))
  have p0001 := (Nominal.classEqRefl (synCres A C))
  have p0002 := (Nominal.classEqRefl (synCres B C))
  have p0003 :=
    @gN3eqtr4g (.classEq A B) (synCin A (synCxp C (synCvv)))
      (synCin B (synCxp C (synCvv))) (synCres A C) (synCres B C) p0000 p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_reseq2`. -/
@[expose]
noncomputable def gReseq2 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (synCres C A) (synCres C B))) :=
  by
  have p0000 := @gXpeq1 A B (synCvv)
  have p0001 :=
    @gIneq2d (.classEq A B) (synCxp A (synCvv)) (synCxp B (synCvv)) C p0000
  have p0002 := (Nominal.classEqRefl (synCres C A))
  have p0003 := (Nominal.classEqRefl (synCres C B))
  have p0004 :=
    @gN3eqtr4g (.classEq A B) (synCin C (synCxp A (synCvv)))
      (synCin C (synCxp B (synCvv))) (synCres C A) (synCres C B) p0001 p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_reseq1i`. -/
@[expose]
noncomputable def gReseq1i (A : Class) (B : Class) (C : Class)
    (hyp_reseqi_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (.classEq (synCres A C) (synCres B C)) :=
  by
  have p0000 := @gReseq1 A B C
  have p0001 := Nominal.mp hyp_reseqi_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_reseq2i`. -/
@[expose]
noncomputable def gReseq2i (A : Class) (B : Class) (C : Class)
    (hyp_reseqi_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (.classEq (synCres C A) (synCres C B)) :=
  by
  have p0000 := @gReseq2 A B C
  have p0001 := Nominal.mp hyp_reseqi_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_reseq12i`. -/
@[expose]
noncomputable def gReseq12i (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_reseqi_1 : Nominal.NPrf (.classEq A B))
    (hyp_reseqi_2 : Nominal.NPrf (.classEq C D)) :
    Nominal.NPrf (.classEq (synCres A C) (synCres B D)) :=
  by
  have p0000 := @gReseq1i A B C hyp_reseqi_1
  have p0001 := @gReseq2i C D B hyp_reseqi_2
  have p0002 := @gEqtri (synCres A C) (synCres B C) (synCres B D) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_reseq2d`. -/
@[expose]
noncomputable def gReseq2d (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_reseqd_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (synCres C A) (synCres C B))) :=
  by
  have p0000 := @gReseq2 A B C
  have p0001 :=
    @gSyl ph (.classEq A B) (.classEq (synCres C A) (synCres C B)) hyp_reseqd_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_imaeq1`. -/
@[expose]
noncomputable def gImaeq1 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (synCima A C) (synCima B C))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  let y : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y_ne_x : y ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have dv_cache_0001 : y ∉ ((Wff.classEq A B)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
          fresh_y_not_A, fresh_y_not_B, or_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((Wff.classEq A B)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
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
  have dv_cache_0005 : x ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_C, not_false_eq_true])
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
  have dv_cache_0007 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show x ≠ y from (by exact fresh_x_ne_y))
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
        simp only [fresh_x_not_B, not_false_eq_true])
  have dv_cache_0009 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_B, not_false_eq_true])
  have p0000 := @gBreq (.cv y) (.cv x) A B
  have p0001 :=
    @gRexbidv (.classEq A B) (synWbr (.cv y) A (.cv x)) (synWbr (.cv y) B (.cv x)) y C
      dv_cache_0001 p0000
  have p0002 :=
    @gAbbidv (.classEq A B) (synWrex y C (synWbr (.cv y) A (.cv x)))
      (synWrex y C (synWbr (.cv y) B (.cv x))) x dv_cache_0002 p0001
  have p0003 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfIma x y A C
      dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfIma x y B C
      dv_cache_0008 dv_cache_0009 dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0005 :=
    @gN3eqtr4g (.classEq A B) (.cab x (synWrex y C (synWbr (.cv y) A (.cv x))))
      (.cab x (synWrex y C (synWbr (.cv y) B (.cv x)))) (synCima A C) (synCima B C)
      p0002 p0003 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_imaeq2`. -/
@[expose]
noncomputable def gImaeq2 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (synCima C A) (synCima C B))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  let y : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y_ne_x : y ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
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
  have dv_cache_0003 : x ∉ ((Wff.classEq A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_C, not_false_eq_true])
  have dv_cache_0005 : y ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_C, not_false_eq_true])
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
  have dv_cache_0007 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show x ≠ y from (by exact fresh_x_ne_y))
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
        simp only [fresh_x_not_B, not_false_eq_true])
  have p0000 := @gRexeq (synWbr (.cv y) C (.cv x)) y A B dv_cache_0001 dv_cache_0002
  have p0001 :=
    @gAbbidv (.classEq A B) (synWrex y A (synWbr (.cv y) C (.cv x)))
      (synWrex y B (synWbr (.cv y) C (.cv x))) x dv_cache_0003 p0000
  have p0002 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfIma x y C A
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0001 dv_cache_0007
  have p0003 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfIma x y C B
      dv_cache_0004 dv_cache_0005 dv_cache_0008 dv_cache_0002 dv_cache_0007
  have p0004 :=
    @gN3eqtr4g (.classEq A B) (.cab x (synWrex y A (synWbr (.cv y) C (.cv x))))
      (.cab x (synWrex y B (synWbr (.cv y) C (.cv x)))) (synCima C A) (synCima C B)
      p0001 p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_imaeq1i`. -/
@[expose]
noncomputable def gImaeq1i (A : Class) (B : Class) (C : Class)
    (hyp_imaeq1i_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (.classEq (synCima A C) (synCima B C)) :=
  by
  have p0000 := @gImaeq1 A B C
  have p0001 := Nominal.mp hyp_imaeq1i_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_imaeq2i`. -/
@[expose]
noncomputable def gImaeq2i (A : Class) (B : Class) (C : Class)
    (hyp_imaeq1i_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (.classEq (synCima C A) (synCima C B)) :=
  by
  have p0000 := @gImaeq2 A B C
  have p0001 := Nominal.mp hyp_imaeq1i_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_imaeq1d`. -/
@[expose]
noncomputable def gImaeq1d (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_imaeq1d_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (synCima A C) (synCima B C))) :=
  by
  have p0000 := @gImaeq1 A B C
  have p0001 :=
    @gSyl ph (.classEq A B) (.classEq (synCima A C) (synCima B C)) hyp_imaeq1d_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_imaeq2d`. -/
@[expose]
noncomputable def gImaeq2d (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_imaeq1d_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (synCima C A) (synCima C B))) :=
  by
  have p0000 := @gImaeq2 A B C
  have p0001 :=
    @gSyl ph (.classEq A B) (.classEq (synCima C A) (synCima C B)) hyp_imaeq1d_1 p0000
  exact p0001


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk011Compact001Part004`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_elimapw1`. -/
@[expose]
noncomputable def gElimapw1 (x : Var) (A : Class) (B : Class) (C : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_C_x : x ∉ C.fv) :
    Nominal.NPrf
      (synWb (.classMem A (synCima B (synCpw1 C)))
        (synWrex x C (.classMem (synCop (synCsn (.cv x)) A) B))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv
  let t : Var := freshVar proofSupport 0
  have fresh_t : t ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_t_ne_x : t ≠ x := by
    intro h
    exact
      fresh_t
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_t : x ≠ t := Ne.symm fresh_t_ne_x
  have fresh_t_not_A : t ∉ A.fv := by
    intro h
    exact
      fresh_t
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_t_not_B : t ∉ B.fv := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_t_not_C : t ∉ C.fv := by
    intro h
    exact fresh_t (Finset.mem_union_right _ (h))
  have dv_cache_0001 : t ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_t_not_A, not_false_eq_true])
  have dv_cache_0002 : t ∉ (B).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_t_not_B, not_false_eq_true])
  have dv_cache_0003 : t ∉ ((synCpw1 C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, fresh_t_not_C,
          not_false_eq_true])
  have dv_cache_0004 : x ∉ ((Class.cv t)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_t, not_false_eq_true])
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
  have dv_cache_0006 : x ∉ ((synWbr (.cv t) B A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_t, dv_A_x, dv_B_x, or_false,
          not_false_eq_true])
  have dv_cache_0007 : t ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_t_not_C, not_false_eq_true])
  have dv_cache_0008 : x ≠ t :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show x ≠ t from (by exact fresh_x_ne_t))
  have dv_cache_0009 : t ∉ ((synCsn (.cv x))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_x,
          not_false_eq_true])
  have dv_cache_0010 : t ∉ ((synWbr (synCsn (.cv x)) B A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_x, fresh_t_not_A, fresh_t_not_B, or_false,
          not_false_eq_true])
  have p0000 := @gElima t A B (synCpw1 C) dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 := (Nominal.biimpRefl (synWrex t (synCpw1 C) (synWbr (.cv t) B A)))
  have p0002 := @gElpw1 x (.cv t) C dv_cache_0004 dv_cache_0005
  have p0003 :=
    @gAnbi1i (.classMem (.cv t) (synCpw1 C))
      (synWrex x C (.classEq (.cv t) (synCsn (.cv x)))) (synWbr (.cv t) B A) p0002
  have p0004 :=
    @gR1941v (.classEq (.cv t) (synCsn (.cv x))) (synWbr (.cv t) B A) x C
      dv_cache_0006
  have p0005 :=
    @gBitr4i (synWa (.classMem (.cv t) (synCpw1 C)) (synWbr (.cv t) B A))
      (synWa (synWrex x C (.classEq (.cv t) (synCsn (.cv x)))) (synWbr (.cv t) B A))
      (synWrex x C (synWa (.classEq (.cv t) (synCsn (.cv x))) (synWbr (.cv t) B A)))
      p0003 p0004
  have p0006 :=
    @gExbii (synWa (.classMem (.cv t) (synCpw1 C)) (synWbr (.cv t) B A))
      (synWrex x C (synWa (.classEq (.cv t) (synCsn (.cv x))) (synWbr (.cv t) B A))) t
      p0005
  have p0007 :=
    @gRexcom4 (synWa (.classEq (.cv t) (synCsn (.cv x))) (synWbr (.cv t) B A)) x t C
      dv_cache_0007 dv_cache_0008
  have p0008 :=
    @gBitr4i (synWex t (synWa (.classMem (.cv t) (synCpw1 C)) (synWbr (.cv t) B A)))
      (synWex t (synWrex x C
          (synWa (.classEq (.cv t) (synCsn (.cv x))) (synWbr (.cv t) B A))))
      (synWrex x C
        (synWex t (synWa (.classEq (.cv t) (synCsn (.cv x))) (synWbr (.cv t) B A))))
      p0006 p0007
  have p0009 :=
    @gBitri (synWrex t (synCpw1 C) (synWbr (.cv t) B A))
      (synWex t (synWa (.classMem (.cv t) (synCpw1 C)) (synWbr (.cv t) B A)))
      (synWrex x C
        (synWex t (synWa (.classEq (.cv t) (synCsn (.cv x))) (synWbr (.cv t) B A))))
      p0001 p0008
  have p0010 := @gSnex (.cv x)
  have p0011 := @gBreq1 (.cv t) (synCsn (.cv x)) A B
  have p0012 :=
    @gCeqsexv (synWbr (.cv t) B A) (synWbr (synCsn (.cv x)) B A) t (synCsn (.cv x))
      dv_cache_0009 dv_cache_0010 p0010 p0011
  have p0013 :=
    @gRexbii
      (synWex t (synWa (.classEq (.cv t) (synCsn (.cv x))) (synWbr (.cv t) B A)))
      (synWbr (synCsn (.cv x)) B A) x C p0012
  have p0014 :=
    @gBitri (synWrex t (synCpw1 C) (synWbr (.cv t) B A))
      (synWrex x C
        (synWex t (synWa (.classEq (.cv t) (synCsn (.cv x))) (synWbr (.cv t) B A))))
      (synWrex x C (synWbr (synCsn (.cv x)) B A)) p0009 p0013
  have p0015 := (Nominal.biimpRefl (synWbr (synCsn (.cv x)) B A))
  have p0016 :=
    @gRexbii (synWbr (synCsn (.cv x)) B A) (.classMem (synCop (synCsn (.cv x)) A) B)
      x C p0015
  have p0017 :=
    @gBitri (synWrex t (synCpw1 C) (synWbr (.cv t) B A))
      (synWrex x C (synWbr (synCsn (.cv x)) B A))
      (synWrex x C (.classMem (synCop (synCsn (.cv x)) A) B)) p0014 p0016
  have p0018 :=
    @gBitri (.classMem A (synCima B (synCpw1 C)))
      (synWrex t (synCpw1 C) (synWbr (.cv t) B A))
      (synWrex x C (.classMem (synCop (synCsn (.cv x)) A) B)) p0000 p0017
  exact p0018

/-- Checked nominal proof certificate identified upstream as `g_elimapw12`. -/
@[expose]
noncomputable def gElimapw12 (x : Var) (A : Class) (B : Class) (C : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_C_x : x ∉ C.fv) :
    Nominal.NPrf
      (synWb (.classMem A (synCima B (synCpw1 (synCpw1 C))))
        (synWrex x C (.classMem (synCop (synCsn (synCsn (.cv x))) A) B))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv
  let t : Var := freshVar proofSupport 0
  have fresh_t : t ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_t_ne_x : t ≠ x := by
    intro h
    exact
      fresh_t
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_t : x ≠ t := Ne.symm fresh_t_ne_x
  have fresh_t_not_A : t ∉ A.fv := by
    intro h
    exact
      fresh_t
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_t_not_B : t ∉ B.fv := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_t_not_C : t ∉ C.fv := by
    intro h
    exact fresh_t (Finset.mem_union_right _ (h))
  have dv_cache_0001 : t ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_t_not_A, not_false_eq_true])
  have dv_cache_0002 : t ∉ (B).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_t_not_B, not_false_eq_true])
  have dv_cache_0003 : t ∉ ((synCpw1 C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, fresh_t_not_C,
          not_false_eq_true])
  have dv_cache_0004 : x ∉ ((Class.cv t)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_t, not_false_eq_true])
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
  have dv_cache_0006 : x ∉ ((Wff.classMem (synCop (synCsn (.cv t)) A) B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_t, dv_A_x, dv_B_x, or_false,
          not_false_eq_true])
  have dv_cache_0007 : t ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_t_not_C, not_false_eq_true])
  have dv_cache_0008 : x ≠ t :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show x ≠ t from (by exact fresh_x_ne_t))
  have dv_cache_0009 : t ∉ ((synCsn (.cv x))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_x,
          not_false_eq_true])
  have dv_cache_0010 :
    t ∉ ((Wff.classMem (synCop (synCsn (synCsn (.cv x))) A) B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_x, fresh_t_not_A, fresh_t_not_B, or_false,
          not_false_eq_true])
  have p0000 := @gElimapw1 t A B (synCpw1 C) dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    (Nominal.biimpRefl (synWrex t (synCpw1 C) (.classMem (synCop (synCsn (.cv t)) A) B)))
  have p0002 := @gElpw1 x (.cv t) C dv_cache_0004 dv_cache_0005
  have p0003 :=
    @gAnbi1i (.classMem (.cv t) (synCpw1 C))
      (synWrex x C (.classEq (.cv t) (synCsn (.cv x))))
      (.classMem (synCop (synCsn (.cv t)) A) B) p0002
  have p0004 :=
    @gR1941v (.classEq (.cv t) (synCsn (.cv x)))
      (.classMem (synCop (synCsn (.cv t)) A) B) x C dv_cache_0006
  have p0005 :=
    @gBitr4i
      (synWa (.classMem (.cv t) (synCpw1 C)) (.classMem (synCop (synCsn (.cv t)) A) B))
      (synWa (synWrex x C (.classEq (.cv t) (synCsn (.cv x))))
        (.classMem (synCop (synCsn (.cv t)) A) B))
      (synWrex x C (synWa (.classEq (.cv t) (synCsn (.cv x)))
          (.classMem (synCop (synCsn (.cv t)) A) B)))
      p0003 p0004
  have p0006 :=
    @gExbii
      (synWa (.classMem (.cv t) (synCpw1 C)) (.classMem (synCop (synCsn (.cv t)) A) B))
      (synWrex x C (synWa (.classEq (.cv t) (synCsn (.cv x)))
          (.classMem (synCop (synCsn (.cv t)) A) B)))
      t p0005
  have p0007 :=
    @gRexcom4
      (synWa (.classEq (.cv t) (synCsn (.cv x))) (.classMem (synCop (synCsn (.cv t)) A) B))
      x t C dv_cache_0007 dv_cache_0008
  have p0008 := @gSnex (.cv x)
  have p0009 := @gSneq (.cv t) (synCsn (.cv x))
  have p0010 :=
    @gOpeq1d (.classEq (.cv t) (synCsn (.cv x))) (synCsn (.cv t))
      (synCsn (synCsn (.cv x))) A p0009
  have p0011 :=
    @gEleq1d (.classEq (.cv t) (synCsn (.cv x))) (synCop (synCsn (.cv t)) A)
      (synCop (synCsn (synCsn (.cv x))) A) B p0010
  have p0012 :=
    @gCeqsexv (.classMem (synCop (synCsn (.cv t)) A) B)
      (.classMem (synCop (synCsn (synCsn (.cv x))) A) B) t (synCsn (.cv x))
      dv_cache_0009 dv_cache_0010 p0008 p0011
  have p0013 :=
    @gRexbii
      (synWex t (synWa (.classEq (.cv t) (synCsn (.cv x)))
          (.classMem (synCop (synCsn (.cv t)) A) B)))
      (.classMem (synCop (synCsn (synCsn (.cv x))) A) B) x C p0012
  have p0014 :=
    @gBitr3i
      (synWex t (synWrex x C (synWa (.classEq (.cv t) (synCsn (.cv x)))
            (.classMem (synCop (synCsn (.cv t)) A) B))))
      (synWrex x C (synWex t (synWa (.classEq (.cv t) (synCsn (.cv x)))
            (.classMem (synCop (synCsn (.cv t)) A) B))))
      (synWrex x C (.classMem (synCop (synCsn (synCsn (.cv x))) A) B)) p0007 p0013
  have p0015 :=
    @gBitri
      (synWex t (synWa (.classMem (.cv t) (synCpw1 C))
          (.classMem (synCop (synCsn (.cv t)) A) B)))
      (synWex t (synWrex x C (synWa (.classEq (.cv t) (synCsn (.cv x)))
            (.classMem (synCop (synCsn (.cv t)) A) B))))
      (synWrex x C (.classMem (synCop (synCsn (synCsn (.cv x))) A) B)) p0006 p0014
  have p0016 :=
    @gBitri (synWrex t (synCpw1 C) (.classMem (synCop (synCsn (.cv t)) A) B))
      (synWex t (synWa (.classMem (.cv t) (synCpw1 C))
          (.classMem (synCop (synCsn (.cv t)) A) B)))
      (synWrex x C (.classMem (synCop (synCsn (synCsn (.cv x))) A) B)) p0001 p0015
  have p0017 :=
    @gBitri (.classMem A (synCima B (synCpw1 (synCpw1 C))))
      (synWrex t (synCpw1 C) (.classMem (synCop (synCsn (.cv t)) A) B))
      (synWrex x C (.classMem (synCop (synCsn (synCsn (.cv x))) A) B)) p0000 p0016
  exact p0017

/-- Checked nominal proof certificate identified upstream as `g_elima1c`. -/
@[expose]
noncomputable def gElima1c (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf
      (synWb (.classMem A (synCima B (synC1c)))
        (synWex x (.classMem (synCop (synCsn (.cv x)) A) B))) :=
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
  have dv_cache_0003 : x ∉ ((synCvv)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have p0000 := @gDf1c2
  have p0001 := @gImaeq2i (synC1c) (synCpw1 (synCvv)) B p0000
  have p0002 := @gEleq2i (synCima B (synC1c)) (synCima B (synCpw1 (synCvv))) A p0001
  have p0003 := @gElimapw1 x A B (synCvv) dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0004 := @gRexv (.classMem (synCop (synCsn (.cv x)) A) B) x
  have p0005 :=
    @gN3bitri (.classMem A (synCima B (synC1c)))
      (.classMem A (synCima B (synCpw1 (synCvv))))
      (synWrex x (synCvv) (.classMem (synCop (synCsn (.cv x)) A) B))
      (synWex x (.classMem (synCop (synCsn (.cv x)) A) B)) p0002 p0003 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_elimapw11c`. -/
@[expose]
noncomputable def gElimapw11c (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf
      (synWb (.classMem A (synCima B (synCpw1 (synC1c))))
        (synWex x (.classMem (synCop (synCsn (synCsn (.cv x))) A) B))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  let t : Var := freshVar proofSupport 0
  have fresh_t : t ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_t_ne_x : t ≠ x := by
    intro h
    exact
      fresh_t
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_t : x ≠ t := Ne.symm fresh_t_ne_x
  have fresh_t_not_A : t ∉ A.fv := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_t_not_B : t ∉ B.fv := by
    intro h
    exact fresh_t (Finset.mem_union_right _ (h))
  have dv_cache_0001 : t ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_t_not_A, not_false_eq_true])
  have dv_cache_0002 : t ∉ (B).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_t_not_B, not_false_eq_true])
  have dv_cache_0003 : t ∉ ((synC1c)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((Class.cv t)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_t, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((Wff.classMem (synCop (synCsn (.cv t)) A) B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_t, dv_A_x, dv_B_x, or_false,
          not_false_eq_true])
  have dv_cache_0006 : t ∉ ((synCsn (.cv x))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_x,
          not_false_eq_true])
  have dv_cache_0007 :
    t ∉ ((Wff.classMem (synCop (synCsn (synCsn (.cv x))) A) B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_x, fresh_t_not_A, fresh_t_not_B, or_false,
          not_false_eq_true])
  have p0000 := @gElimapw1 t A B (synC1c) dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    (Nominal.biimpRefl (synWrex t (synC1c) (.classMem (synCop (synCsn (.cv t)) A) B)))
  have p0002 := @gEl1c x (.cv t) dv_cache_0004
  have p0003 :=
    @gAnbi1i (.classMem (.cv t) (synC1c))
      (synWex x (.classEq (.cv t) (synCsn (.cv x))))
      (.classMem (synCop (synCsn (.cv t)) A) B) p0002
  have p0004 :=
    @gN1941v (.classEq (.cv t) (synCsn (.cv x)))
      (.classMem (synCop (synCsn (.cv t)) A) B) x dv_cache_0005
  have p0005 :=
    @gBitr4i
      (synWa (.classMem (.cv t) (synC1c)) (.classMem (synCop (synCsn (.cv t)) A) B))
      (synWa (synWex x (.classEq (.cv t) (synCsn (.cv x))))
        (.classMem (synCop (synCsn (.cv t)) A) B))
      (synWex x (synWa (.classEq (.cv t) (synCsn (.cv x)))
          (.classMem (synCop (synCsn (.cv t)) A) B)))
      p0003 p0004
  have p0006 :=
    @gExbii
      (synWa (.classMem (.cv t) (synC1c)) (.classMem (synCop (synCsn (.cv t)) A) B))
      (synWex x (synWa (.classEq (.cv t) (synCsn (.cv x)))
          (.classMem (synCop (synCsn (.cv t)) A) B)))
      t p0005
  have p0007 :=
    @gExcom
      (synWa (.classEq (.cv t) (synCsn (.cv x))) (.classMem (synCop (synCsn (.cv t)) A) B))
      t x
  have p0008 :=
    @gBitri
      (synWex t (synWa (.classMem (.cv t) (synC1c))
          (.classMem (synCop (synCsn (.cv t)) A) B)))
      (synWex t (synWex x (synWa (.classEq (.cv t) (synCsn (.cv x)))
            (.classMem (synCop (synCsn (.cv t)) A) B))))
      (synWex x (synWex t (synWa (.classEq (.cv t) (synCsn (.cv x)))
            (.classMem (synCop (synCsn (.cv t)) A) B))))
      p0006 p0007
  have p0009 := @gSnex (.cv x)
  have p0010 := @gSneq (.cv t) (synCsn (.cv x))
  have p0011 :=
    @gOpeq1d (.classEq (.cv t) (synCsn (.cv x))) (synCsn (.cv t))
      (synCsn (synCsn (.cv x))) A p0010
  have p0012 :=
    @gEleq1d (.classEq (.cv t) (synCsn (.cv x))) (synCop (synCsn (.cv t)) A)
      (synCop (synCsn (synCsn (.cv x))) A) B p0011
  have p0013 :=
    @gCeqsexv (.classMem (synCop (synCsn (.cv t)) A) B)
      (.classMem (synCop (synCsn (synCsn (.cv x))) A) B) t (synCsn (.cv x))
      dv_cache_0006 dv_cache_0007 p0009 p0012
  have p0014 :=
    @gExbii
      (synWex t (synWa (.classEq (.cv t) (synCsn (.cv x)))
          (.classMem (synCop (synCsn (.cv t)) A) B)))
      (.classMem (synCop (synCsn (synCsn (.cv x))) A) B) x p0013
  have p0015 :=
    @gN3bitri (synWrex t (synC1c) (.classMem (synCop (synCsn (.cv t)) A) B))
      (synWex t (synWa (.classMem (.cv t) (synC1c))
          (.classMem (synCop (synCsn (.cv t)) A) B)))
      (synWex x (synWex t (synWa (.classEq (.cv t) (synCsn (.cv x)))
            (.classMem (synCop (synCsn (.cv t)) A) B))))
      (synWex x (.classMem (synCop (synCsn (synCsn (.cv x))) A) B)) p0001 p0008 p0014
  have p0016 :=
    @gBitri (.classMem A (synCima B (synCpw1 (synC1c))))
      (synWrex t (synC1c) (.classMem (synCop (synCsn (.cv t)) A) B))
      (synWex x (.classMem (synCop (synCsn (synCsn (.cv x))) A) B)) p0000 p0015
  exact p0016

/-- Checked nominal proof certificate identified upstream as `g_brres`. -/
@[expose]
noncomputable def gBrres (A : Class) (B : Class) (C : Class) (D : Class) :
    Nominal.NPrf
      (synWb (synWbr A (synCres C D) B) (synWa (synWbr A C B) (.classMem A D))) :=
  by
  have p0000 := (Nominal.classEqRefl (synCres C D))
  have p0001 := @gBreqi A B (synCres C D) (synCin C (synCxp D (synCvv))) p0000
  have p0002 := @gBrin A B C (synCxp D (synCvv))
  have p0003 := @gAnass (synWbr A C B) (.classMem A D) (.classMem B (synCvv))
  have p0004 := @gBrex A B C
  have p0005 :=
    @gSimprd (synWbr A C B) (.classMem A (synCvv)) (.classMem B (synCvv)) p0004
  have p0006 := @gAdantr (synWbr A C B) (.classMem B (synCvv)) (.classMem A D) p0005
  have p0007 :=
    @gPm471i (synWa (synWbr A C B) (.classMem A D)) (.classMem B (synCvv)) p0006
  have p0008 := @gBrxp A B D (synCvv)
  have p0009 :=
    @gAnbi2i (synWbr A (synCxp D (synCvv)) B)
      (synWa (.classMem A D) (.classMem B (synCvv))) (synWbr A C B) p0008
  have p0010 :=
    @gN3bitr4ri
      (synWa (synWa (synWbr A C B) (.classMem A D)) (.classMem B (synCvv)))
      (synWa (synWbr A C B) (synWa (.classMem A D) (.classMem B (synCvv))))
      (synWa (synWbr A C B) (.classMem A D))
      (synWa (synWbr A C B) (synWbr A (synCxp D (synCvv)) B)) p0003 p0007 p0009
  have p0011 :=
    @gN3bitri (synWbr A (synCres C D) B)
      (synWbr A (synCin C (synCxp D (synCvv))) B)
      (synWa (synWbr A C B) (synWbr A (synCxp D (synCvv)) B))
      (synWa (synWbr A C B) (.classMem A D)) p0001 p0002 p0010
  exact p0011

/-- Checked nominal proof certificate identified upstream as `g_opelres`. -/
@[expose]
noncomputable def gOpelres (A : Class) (B : Class) (C : Class) (D : Class) :
    Nominal.NPrf
      (synWb (.classMem (synCop A B) (synCres C D))
        (synWa (.classMem (synCop A B) C) (.classMem A D))) :=
  by
  have p0000 := @gBrres A B C D
  have p0001 := (Nominal.biimpRefl (synWbr A (synCres C D) B))
  have p0002 := (Nominal.biimpRefl (synWbr A C B))
  have p0003 :=
    @gAnbi1i (synWbr A C B) (.classMem (synCop A B) C) (.classMem A D) p0002
  have p0004 :=
    @gN3bitr3i (synWbr A (synCres C D) B) (synWa (synWbr A C B) (.classMem A D))
      (.classMem (synCop A B) (synCres C D))
      (synWa (.classMem (synCop A B) C) (.classMem A D)) p0000 p0001 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_dfima3`. -/
@[expose]
noncomputable def gDfima3 (A : Class) (B : Class) :
    Nominal.NPrf (.classEq (synCima A B) (synCrn (synCres A B))) :=
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
  have dv_cache_0001 : y ∉ ((Class.cv x)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_x, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((synCres A B)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          Finset.mem_union, fresh_y_not_A, fresh_y_not_B, or_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
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
  have dv_cache_0005 : x ∉ ((synCima A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          Finset.mem_union, fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true])
  have dv_cache_0006 : x ∉ ((synCrn (synCres A B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true])
  have p0000 := @gOpelres (.cv y) (.cv x) A B
  have p0001 := @gAncom (.classMem (synCop (.cv y) (.cv x)) A) (.classMem (.cv y) B)
  have p0002 :=
    @gBitri (.classMem (synCop (.cv y) (.cv x)) (synCres A B))
      (synWa (.classMem (synCop (.cv y) (.cv x)) A) (.classMem (.cv y) B))
      (synWa (.classMem (.cv y) B) (.classMem (synCop (.cv y) (.cv x)) A)) p0000 p0001
  have p0003 :=
    @gExbii (.classMem (synCop (.cv y) (.cv x)) (synCres A B))
      (synWa (.classMem (.cv y) B) (.classMem (synCop (.cv y) (.cv x)) A)) y p0002
  have p0004 := @gElrn2 y (.cv x) (synCres A B) dv_cache_0001 dv_cache_0002
  have p0005 := @gElima3 y (.cv x) A B dv_cache_0001 dv_cache_0003 dv_cache_0004
  have p0006 :=
    @gN3bitr4ri (synWex y (.classMem (synCop (.cv y) (.cv x)) (synCres A B)))
      (synWex y (synWa (.classMem (.cv y) B) (.classMem (synCop (.cv y) (.cv x)) A)))
      (.classMem (.cv x) (synCrn (synCres A B))) (.classMem (.cv x) (synCima A B))
      p0003 p0004 p0005
  have p0007 :=
    @gEqriv x (synCima A B) (synCrn (synCres A B)) dv_cache_0005 dv_cache_0006 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_dfima4`. -/
@[expose]
noncomputable def gDfima4 (x : Var) (y : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.classEq (synCima A B) (.cab y (synWex x
            (synWa (.classMem (.cv x) B) (.classMem (synCop (.cv x) (.cv y)) A))))) :=
  by
  have dv_cache_0001 : y ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_y, not_false_eq_true])
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
  have dv_cache_0005 : y ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show y ≠ x from (by exact Ne.symm dv_x_y))
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfIma y x A B
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0001 := (Nominal.biimpRefl (synWbr (.cv x) A (.cv y)))
  have p0002 :=
    @gRexbii (synWbr (.cv x) A (.cv y)) (.classMem (synCop (.cv x) (.cv y)) A) x B
      p0001
  have p0003 := (Nominal.biimpRefl (synWrex x B (.classMem (synCop (.cv x) (.cv y)) A)))
  have p0004 :=
    @gBitri (synWrex x B (synWbr (.cv x) A (.cv y)))
      (synWrex x B (.classMem (synCop (.cv x) (.cv y)) A))
      (synWex x (synWa (.classMem (.cv x) B) (.classMem (synCop (.cv x) (.cv y)) A)))
      p0002 p0003
  have p0005 :=
    @gAbbii (synWrex x B (synWbr (.cv x) A (.cv y)))
      (synWex x (synWa (.classMem (.cv x) B) (.classMem (synCop (.cv x) (.cv y)) A))) y
      p0004
  have p0006 :=
    @gEqtri (synCima A B) (.cab y (synWrex x B (synWbr (.cv x) A (.cv y))))
      (.cab y (synWex x
          (synWa (.classMem (.cv x) B) (.classMem (synCop (.cv x) (.cv y)) A))))
      p0000 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_rneq`. -/
@[expose]
noncomputable def gRneq (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (synCrn A) (synCrn B))) :=
  by
  have p0000 := @gImaeq1 A B (synCvv)
  have p0001 := (Nominal.classEqRefl (synCrn A))
  have p0002 := (Nominal.classEqRefl (synCrn B))
  have p0003 :=
    @gN3eqtr4g (.classEq A B) (synCima A (synCvv)) (synCima B (synCvv)) (synCrn A)
      (synCrn B) p0000 p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_rneqi`. -/
@[expose]
noncomputable def gRneqi (A : Class) (B : Class)
    (hyp_rneqi_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (.classEq (synCrn A) (synCrn B)) :=
  by
  have p0000 := @gRneq A B
  have p0001 := Nominal.mp hyp_rneqi_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_rneqd`. -/
@[expose]
noncomputable def gRneqd (ph : Wff) (A : Class) (B : Class)
    (hyp_rneqd_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (synCrn A) (synCrn B))) :=
  by
  have p0000 := @gRneq A B
  have p0001 :=
    @gSyl ph (.classEq A B) (.classEq (synCrn A) (synCrn B)) hyp_rneqd_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_rnss`. -/
@[expose]
noncomputable def gRnss (A : Class) (B : Class) :
    Nominal.NPrf (.imp (synWss A B) (synWss (synCrn A) (synCrn B))) :=
  by
  have p0000 := @gCnvss A B
  have p0001 := @gDmss (synCcnv A) (synCcnv B)
  have p0002 :=
    @gSyl (synWss A B) (synWss (synCcnv A) (synCcnv B))
      (synWss (synCdm (synCcnv A)) (synCdm (synCcnv B))) p0000 p0001
  have p0003 := @gDfrn4 A
  have p0004 := @gDfrn4 B
  have p0005 :=
    @gN3sstr4g (synWss A B) (synCdm (synCcnv A)) (synCdm (synCcnv B)) (synCrn A)
      (synCrn B) p0002 p0003 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_brelrn`. -/
@[expose]
noncomputable def gBrelrn (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (synWbr A C B) (.classMem B (synCrn C))) :=
  by
  have p0000 := @gBreldm B A (synCcnv C)
  have p0001 := @gBrcnv B A C
  have p0002 := @gBicomi (synWbr B (synCcnv C) A) (synWbr A C B) p0001
  have p0003 := @gDfrn4 C
  have p0004 := @gEleq2i (synCrn C) (synCdm (synCcnv C)) B p0003
  have p0005 :=
    @gN3imtr4i (synWbr B (synCcnv C) A) (.classMem B (synCdm (synCcnv C)))
      (synWbr A C B) (.classMem B (synCrn C)) p0000 p0002 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_opelrn`. -/
@[expose]
noncomputable def gOpelrn (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classMem (synCop A B) C) (.classMem B (synCrn C))) :=
  by
  have p0000 := (Nominal.biimpRefl (synWbr A C B))
  have p0001 := @gBrelrn A B C
  have p0002 :=
    @gSylbir (.classMem (synCop A B) C) (synWbr A C B) (.classMem B (synCrn C)) p0000
      p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_dfrnf`. -/
@[expose]
noncomputable def gDfrnf (x : Var) (y : Var) (A : Class) (dv_x_y : x ≠ y)
    (hyp_dfrnf_1 : Nominal.NPrf (synWnfc x A))
    (hyp_dfrnf_2 : Nominal.NPrf (synWnfc y A)) :
    Nominal.NPrf
      (.classEq (synCrn A) (.cab y (synWex x (synWbr (.cv x) A (.cv y))))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv
  let v : Var := freshVar proofSupport 0
  let w : Var := freshVar proofSupport 1
  have fresh_v : v ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_v_ne_x : v ≠ x := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_v : x ≠ v := Ne.symm fresh_v_ne_x
  have fresh_v_not_A : v ∉ A.fv := by
    intro h
    exact fresh_v (Finset.mem_union_right _ (h))
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
  have fresh_w_ne_y : w ≠ y := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_y_ne_w : y ≠ w := Ne.symm fresh_w_ne_y
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have fresh_v_ne_w : v ≠ w :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : v ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_v_not_A, not_false_eq_true])
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
  have dv_cache_0003 : v ≠ w :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show v ≠ w from (by exact fresh_v_ne_w))
  have dv_cache_0004 : x ∉ ((Class.cv v)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_v, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((Class.cv w)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_w, not_false_eq_true])
  have dv_cache_0006 : v ∉ ((synWbr (.cv x) A (.cv w))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_v_ne_x, fresh_v_ne_w, fresh_v_not_A, or_false,
          not_false_eq_true])
  have dv_cache_0007 : y ∉ ((Class.cv x)).fv :=
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
          (Ne.symm dv_x_y), not_false_eq_true])
  have dv_cache_0008 : y ∉ ((Class.cv w)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_w, not_false_eq_true])
  have dv_cache_0009 : w ∉ ((synWex x (synWbr (.cv x) A (.cv y)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_w_ne_x, fresh_w_ne_y, fresh_w_not_A, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0010 : x ∉ ((Wff.classEq (.cv w) (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_w, dv_x_y, or_false, not_false_eq_true])
  have p0000 := @gDfrn2 v w A dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 := @gNfcv x (.cv v) dv_cache_0004
  have p0002 := @gNfcv x (.cv w) dv_cache_0005
  have p0003 := @gNfbr x (.cv v) (.cv w) A p0001 hyp_dfrnf_1 p0002
  have p0004 := @gNfv (synWbr (.cv x) A (.cv w)) v dv_cache_0006
  have p0005 := @gBreq1 (.cv v) (.cv x) (.cv w) A
  have p0006_e02_recanon :
    Nominal.NPrf
      (.imp (.objEq v x) (synWb (synWbr (.cv v) A (.cv w)) (synWbr (.cv x) A (.cv w)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWbr synCop synCun synCnin synWnan synWa synCcompl synWrex
          synWex synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0005
  have p0006 :=
    @gCbvex (synWbr (.cv v) A (.cv w)) (synWbr (.cv x) A (.cv w)) v x p0003 p0004
      p0006_e02_recanon
  have p0007 :=
    @gAbbii (synWex v (synWbr (.cv v) A (.cv w)))
      (synWex x (synWbr (.cv x) A (.cv w))) w p0006
  have p0008 := @gNfcv y (.cv x) dv_cache_0007
  have p0009 := @gNfcv y (.cv w) dv_cache_0008
  have p0010 := @gNfbr y (.cv x) (.cv w) A p0008 hyp_dfrnf_2 p0009
  have p0011 := @gNfex (synWbr (.cv x) A (.cv w)) y x p0010
  have p0012 := @gNfv (synWex x (synWbr (.cv x) A (.cv y))) w dv_cache_0009
  have p0013 := @gBreq2 (.cv w) (.cv y) (.cv x) A
  have p0014 :=
    @gExbidv (.classEq (.cv w) (.cv y)) (synWbr (.cv x) A (.cv w))
      (synWbr (.cv x) A (.cv y)) x dv_cache_0010 p0013
  have p0015_e02_recanon :
    Nominal.NPrf
      (.imp (.objEq w y) (synWb (synWex x (synWbr (.cv x) A (.cv w)))
          (synWex x (synWbr (.cv x) A (.cv y))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWex synWbr synCop synCun synCnin synWnan synWa synCcompl
          synWrex synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0014
  have p0015 :=
    @gCbvab (synWex x (synWbr (.cv x) A (.cv w)))
      (synWex x (synWbr (.cv x) A (.cv y))) w y p0011 p0012 p0015_e02_recanon
  have p0016 :=
    @gN3eqtri (synCrn A) (.cab w (synWex v (synWbr (.cv v) A (.cv w))))
      (.cab w (synWex x (synWbr (.cv x) A (.cv w))))
      (.cab y (synWex x (synWbr (.cv x) A (.cv y)))) p0000 p0007 p0015
  exact p0016

/-- Checked nominal proof certificate identified upstream as `g_rnopab`. -/
@[expose]
noncomputable def gRnopab (ph : Wff) (x : Var) (y : Var) (dv_x_y : x ≠ y) :
    Nominal.NPrf (.classEq (synCrn (synCopab x y ph)) (.cab y (synWex x ph))) :=
  by
  have dv_cache_0001 : x ≠ y := by exact (show x ≠ y from (by exact dv_x_y))
  have p0000 := @gNfopab1 ph x y
  have p0001 := @gNfopab2 ph x y
  have p0002 := @gDfrnf x y (synCopab x y ph) dv_cache_0001 p0000 p0001
  have p0003 := (Nominal.biimpRefl (synWbr (.cv x) (synCopab x y ph) (.cv y)))
  have p0004 := @gOpabid ph x y
  have p0005 :=
    @gBitri (synWbr (.cv x) (synCopab x y ph) (.cv y))
      (.classMem (synCop (.cv x) (.cv y)) (synCopab x y ph)) ph p0003 p0004
  have p0006 := @gExbii (synWbr (.cv x) (synCopab x y ph) (.cv y)) ph x p0005
  have p0007 :=
    @gAbbii (synWex x (synWbr (.cv x) (synCopab x y ph) (.cv y))) (synWex x ph) y
      p0006
  have p0008 :=
    @gEqtri (synCrn (synCopab x y ph))
      (.cab y (synWex x (synWbr (.cv x) (synCopab x y ph) (.cv y))))
      (.cab y (synWex x ph)) p0002 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_rnopab2`. -/
@[expose]
noncomputable def gRnopab2 (x : Var) (y : Var) (A : Class) (B : Class) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.classEq (synCrn (synCopab x y (synWa (.classMem (.cv x) A) (.classEq (.cv y) B))))
        (.cab y (synWrex x A (.classEq (.cv y) B)))) :=
  by
  have dv_cache_0001 : x ≠ y := by exact (show x ≠ y from (by exact dv_x_y))
  have p0000 :=
    @gRnopab (synWa (.classMem (.cv x) A) (.classEq (.cv y) B)) x y dv_cache_0001
  have p0001 := (Nominal.biimpRefl (synWrex x A (.classEq (.cv y) B)))
  have p0002 :=
    @gAbbii (synWrex x A (.classEq (.cv y) B))
      (synWex x (synWa (.classMem (.cv x) A) (.classEq (.cv y) B))) y p0001
  have p0003 :=
    @gEqtr4i
      (synCrn (synCopab x y (synWa (.classMem (.cv x) A) (.classEq (.cv y) B))))
      (.cab y (synWex x (synWa (.classMem (.cv x) A) (.classEq (.cv y) B))))
      (.cab y (synWrex x A (.classEq (.cv y) B))) p0000 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_rn0`. -/
@[expose]
noncomputable def gRn0 : Nominal.NPrf (.classEq (synCrn (synC0)) (synC0)) :=
  by
  have p0000 := @gDm0
  have p0001 := @gDm0rn0 (synC0)
  have p0002 :=
    @gMpbi (.classEq (synCdm (synC0)) (synC0)) (.classEq (synCrn (synC0)) (synC0))
      p0000 p0001
  exact p0002


end NFChoice.DirectNominalPrf.WPPReplay

end

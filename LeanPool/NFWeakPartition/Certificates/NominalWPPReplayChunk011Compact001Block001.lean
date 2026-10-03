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

@[expose]
noncomputable def g_coeq2i (A : Class) (B : Class) (C : Class)
    (hyp_coeq1i_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (.classEq (syn_ccom C A) (syn_ccom C B)) :=
  by
  have p0000 := @g_coeq2 A B C
  have p0001 := Nominal.mp hyp_coeq1i_1 p0000
  exact p0001

@[expose]
noncomputable def g_coeq1d (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_coeq1d_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (syn_ccom A C) (syn_ccom B C))) :=
  by
  have p0000 := @g_coeq1 A B C
  have p0001 :=
    @g_syl ph (.classEq A B) (.classEq (syn_ccom A C) (syn_ccom B C)) hyp_coeq1d_1 p0000
  exact p0001

@[expose]
noncomputable def g_coeq2d (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_coeq1d_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (syn_ccom C A) (syn_ccom C B))) :=
  by
  have p0000 := @g_coeq2 A B C
  have p0001 :=
    @g_syl ph (.classEq A B) (.classEq (syn_ccom C A) (syn_ccom C B)) hyp_coeq1d_1 p0000
  exact p0001

@[expose]
noncomputable def g_coeq12i (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_coeq12i_1 : Nominal.NPrf (.classEq A B))
    (hyp_coeq12i_2 : Nominal.NPrf (.classEq C D)) :
    Nominal.NPrf (.classEq (syn_ccom A C) (syn_ccom B D)) :=
  by
  have p0000 := @g_coeq1i A B C hyp_coeq12i_1
  have p0001 := @g_coeq2i C D B hyp_coeq12i_2
  have p0002 := @g_eqtri (syn_ccom A C) (syn_ccom B C) (syn_ccom B D) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_coeq12d (ph : Wff) (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_coeq12d_1 : Nominal.NPrf (.imp ph (.classEq A B)))
    (hyp_coeq12d_2 : Nominal.NPrf (.imp ph (.classEq C D))) :
    Nominal.NPrf (.imp ph (.classEq (syn_ccom A C) (syn_ccom B D))) :=
  by
  have p0000 := @g_coeq1d ph A B C hyp_coeq12d_1
  have p0001 := @g_coeq2d ph C D B hyp_coeq12d_2
  have p0002 := @g_eqtrd ph (syn_ccom A C) (syn_ccom B C) (syn_ccom B D) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_brco (x : Var) (A : Class) (B : Class) (C : Class) (D : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_C_x : x ∉ C.fv) (dv_D_x : x ∉ D.fv) :
    Nominal.NPrf
      (syn_wb (syn_wbr A (syn_ccom C D) B)
        (syn_wex x (syn_wa (syn_wbr A D (.cv x)) (syn_wbr (.cv x) C B)))) :=
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
    x ∉ ((syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv)))).fv := by
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
    y ∉ ((syn_wex x (syn_wa (syn_wbr A D (.cv x)) (syn_wbr (.cv x) C B)))).fv :=
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
    z ∉ ((syn_wex x (syn_wa (syn_wbr A D (.cv x)) (syn_wbr (.cv x) C B)))).fv :=
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
  have p0000 := @g_brex A B (syn_ccom C D)
  have p0001 := @g_brex A (.cv x) D
  have p0002 :=
    @g_simpld (syn_wbr A D (.cv x)) (.classMem A (syn_cvv)) (.classMem (.cv x) (syn_cvv))
      p0001
  have p0003 := @g_brex (.cv x) B C
  have p0004 :=
    @g_simprd (syn_wbr (.cv x) C B) (.classMem (.cv x) (syn_cvv)) (.classMem B (syn_cvv))
      p0003
  have p0005 :=
    @g_anim12i (syn_wbr A D (.cv x)) (.classMem A (syn_cvv)) (syn_wbr (.cv x) C B)
      (.classMem B (syn_cvv)) p0002 p0004
  have p0006 :=
    @g_exlimiv (syn_wa (syn_wbr A D (.cv x)) (syn_wbr (.cv x) C B))
      (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv))) x dv_cache_0001 p0005
  have p0007 := @g_breq1 (.cv y) A (.cv x) D
  have p0008 :=
    @g_anbi1d (.classEq (.cv y) A) (syn_wbr (.cv y) D (.cv x)) (syn_wbr A D (.cv x))
      (syn_wbr (.cv x) C (.cv z)) p0007
  have p0009 :=
    @g_exbidv (.classEq (.cv y) A)
      (syn_wa (syn_wbr (.cv y) D (.cv x)) (syn_wbr (.cv x) C (.cv z)))
      (syn_wa (syn_wbr A D (.cv x)) (syn_wbr (.cv x) C (.cv z))) x dv_cache_0002 p0008
  have p0010 := @g_breq2 (.cv z) B (.cv x) C
  have p0011 :=
    @g_anbi2d (.classEq (.cv z) B) (syn_wbr (.cv x) C (.cv z)) (syn_wbr (.cv x) C B)
      (syn_wbr A D (.cv x)) p0010
  have p0012 :=
    @g_exbidv (.classEq (.cv z) B)
      (syn_wa (syn_wbr A D (.cv x)) (syn_wbr (.cv x) C (.cv z)))
      (syn_wa (syn_wbr A D (.cv x)) (syn_wbr (.cv x) C B)) x dv_cache_0003 p0011
  have p0013 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_co y z x C D
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
      dv_cache_0010 dv_cache_0011 dv_cache_0012
  have p0014 :=
    @g_brabg (syn_wex x (syn_wa (syn_wbr (.cv y) D (.cv x)) (syn_wbr (.cv x) C (.cv z))))
      (syn_wex x (syn_wa (syn_wbr A D (.cv x)) (syn_wbr (.cv x) C (.cv z))))
      (syn_wex x (syn_wa (syn_wbr A D (.cv x)) (syn_wbr (.cv x) C B))) y z A B (syn_cvv)
      (syn_cvv) (syn_ccom C D) dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
      dv_cache_0017 dv_cache_0018 dv_cache_0010 p0009 p0012 p0013
  have p0015 :=
    @g_pm5_21nii (syn_wbr A (syn_ccom C D) B)
      (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv)))
      (syn_wex x (syn_wa (syn_wbr A D (.cv x)) (syn_wbr (.cv x) C B))) p0000 p0006 p0014
  exact p0015

@[expose]
noncomputable def g_opelco (x : Var) (A : Class) (B : Class) (C : Class) (D : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_C_x : x ∉ C.fv) (dv_D_x : x ∉ D.fv) :
    Nominal.NPrf
      (syn_wb (.classMem (syn_cop A B) (syn_ccom C D))
        (syn_wex x (syn_wa (syn_wbr A D (.cv x)) (syn_wbr (.cv x) C B)))) :=
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
  have p0000 := (Nominal.biimpRefl (syn_wbr A (syn_ccom C D) B))
  have p0001 := @g_brco x A B C D dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0002 :=
    @g_bitr3i (.classMem (syn_cop A B) (syn_ccom C D)) (syn_wbr A (syn_ccom C D) B)
      (syn_wex x (syn_wa (syn_wbr A D (.cv x)) (syn_wbr (.cv x) C B))) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_cnvss (A : Class) (B : Class) :
    Nominal.NPrf (.imp (syn_wss A B) (syn_wss (syn_ccnv A) (syn_ccnv B))) :=
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
  have dv_cache_0001 : x ∉ ((syn_wss A B)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_wss A B)).fv :=
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
  have p0000 := @g_ssel A B (syn_cop (.cv y) (.cv x))
  have p0001 := (Nominal.biimpRefl (syn_wbr (.cv y) A (.cv x)))
  have p0002 := (Nominal.biimpRefl (syn_wbr (.cv y) B (.cv x)))
  have p0003 :=
    @g_n_3imtr4g (syn_wss A B) (.classMem (syn_cop (.cv y) (.cv x)) A)
      (.classMem (syn_cop (.cv y) (.cv x)) B) (syn_wbr (.cv y) A (.cv x))
      (syn_wbr (.cv y) B (.cv x)) p0000 p0001 p0002
  have p0004 :=
    @g_ssopab2dv (syn_wss A B) (syn_wbr (.cv y) A (.cv x)) (syn_wbr (.cv y) B (.cv x)) x y
      dv_cache_0001 dv_cache_0002 p0003
  have p0005 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_cnv x y A
      dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0006 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_cnv x y B
      dv_cache_0006 dv_cache_0007 dv_cache_0005
  have p0007 :=
    @g_n_3sstr4g (syn_wss A B) (syn_copab x y (syn_wbr (.cv y) A (.cv x)))
      (syn_copab x y (syn_wbr (.cv y) B (.cv x))) (syn_ccnv A) (syn_ccnv B) p0004 p0005
      p0006
  exact p0007

@[expose]
noncomputable def g_cnveq (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_ccnv A) (syn_ccnv B))) :=
  by
  have p0000 := @g_cnvss A B
  have p0001 := @g_cnvss B A
  have p0002 :=
    @g_anim12i (syn_wss A B) (syn_wss (syn_ccnv A) (syn_ccnv B)) (syn_wss B A)
      (syn_wss (syn_ccnv B) (syn_ccnv A)) p0000 p0001
  have p0003 := @g_eqss A B
  have p0004 := @g_eqss (syn_ccnv A) (syn_ccnv B)
  have p0005 :=
    @g_n_3imtr4i (syn_wa (syn_wss A B) (syn_wss B A))
      (syn_wa (syn_wss (syn_ccnv A) (syn_ccnv B)) (syn_wss (syn_ccnv B) (syn_ccnv A)))
      (.classEq A B) (.classEq (syn_ccnv A) (syn_ccnv B)) p0002 p0003 p0004
  exact p0005

@[expose]
noncomputable def g_cnveqi (A : Class) (B : Class)
    (hyp_cnveqi_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (.classEq (syn_ccnv A) (syn_ccnv B)) :=
  by
  have p0000 := @g_cnveq A B
  have p0001 := Nominal.mp hyp_cnveqi_1 p0000
  exact p0001

@[expose]
noncomputable def g_cnveqd (ph : Wff) (A : Class) (B : Class)
    (hyp_cnveqd_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (syn_ccnv A) (syn_ccnv B))) :=
  by
  have p0000 := @g_cnveq A B
  have p0001 :=
    @g_syl ph (.classEq A B) (.classEq (syn_ccnv A) (syn_ccnv B)) hyp_cnveqd_1 p0000
  exact p0001

@[expose]
noncomputable def g_elcnv (x : Var) (y : Var) (A : Class) (R : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_R_x : x ∉ R.fv) (dv_R_y : y ∉ R.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (syn_wb (.classMem A (syn_ccnv R)) (syn_wex x (syn_wex y
            (syn_wa (.classEq A (syn_cop (.cv x) (.cv y))) (syn_wbr (.cv y) R (.cv x)))))) :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_cnv x y R
      dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 := @g_eleq2i (syn_ccnv R) (syn_copab x y (syn_wbr (.cv y) R (.cv x))) A p0000
  have p0002 := @g_elopab (syn_wbr (.cv y) R (.cv x)) x y A dv_cache_0004 dv_cache_0005
  have p0003 :=
    @g_bitri (.classMem A (syn_ccnv R))
      (.classMem A (syn_copab x y (syn_wbr (.cv y) R (.cv x))))
      (syn_wex x (syn_wex y
          (syn_wa (.classEq A (syn_cop (.cv x) (.cv y))) (syn_wbr (.cv y) R (.cv x)))))
      p0001 p0002
  exact p0003

@[expose]
noncomputable def g_elcnv2 (x : Var) (y : Var) (A : Class) (R : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_R_x : x ∉ R.fv) (dv_R_y : y ∉ R.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (syn_wb (.classMem A (syn_ccnv R)) (syn_wex x (syn_wex y
            (syn_wa (.classEq A (syn_cop (.cv x) (.cv y)))
              (.classMem (syn_cop (.cv y) (.cv x)) R))))) :=
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
    @g_elcnv x y A R dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0001 := (Nominal.biimpRefl (syn_wbr (.cv y) R (.cv x)))
  have p0002 :=
    @g_anbi2i (syn_wbr (.cv y) R (.cv x)) (.classMem (syn_cop (.cv y) (.cv x)) R)
      (.classEq A (syn_cop (.cv x) (.cv y))) p0001
  have p0003 :=
    @g_n_2exbii
      (syn_wa (.classEq A (syn_cop (.cv x) (.cv y))) (syn_wbr (.cv y) R (.cv x)))
      (syn_wa (.classEq A (syn_cop (.cv x) (.cv y))) (.classMem (syn_cop (.cv y) (.cv x)) R))
      x y p0002
  have p0004 :=
    @g_bitri (.classMem A (syn_ccnv R))
      (syn_wex x (syn_wex y
          (syn_wa (.classEq A (syn_cop (.cv x) (.cv y))) (syn_wbr (.cv y) R (.cv x)))))
      (syn_wex x (syn_wex y (syn_wa (.classEq A (syn_cop (.cv x) (.cv y)))
            (.classMem (syn_cop (.cv y) (.cv x)) R))))
      p0000 p0003
  exact p0004

@[expose]
noncomputable def g_brcnv (A : Class) (B : Class) (R : Class) :
    Nominal.NPrf (syn_wb (syn_wbr A (syn_ccnv R) B) (syn_wbr B R A)) :=
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
  have dv_cache_0008 : x ∉ ((syn_wbr B R A)).fv :=
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
  have dv_cache_0009 : y ∉ ((syn_wbr B R A)).fv :=
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
  have p0000 := @g_brex A B (syn_ccnv R)
  have p0001 := @g_brex B A R
  have p0002 :=
    @g_ancomd (syn_wbr B R A) (.classMem B (syn_cvv)) (.classMem A (syn_cvv)) p0001
  have p0003 := @g_breq2 (.cv x) A (.cv y) R
  have p0004 := @g_breq1 (.cv y) B A R
  have p0005 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_cnv x y R
      dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0006 :=
    @g_brabg (syn_wbr (.cv y) R (.cv x)) (syn_wbr (.cv y) R A) (syn_wbr B R A) x y A B
      (syn_cvv) (syn_cvv) (syn_ccnv R) dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0003 p0003 p0004 p0005
  have p0007 :=
    @g_pm5_21nii (syn_wbr A (syn_ccnv R) B)
      (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv))) (syn_wbr B R A) p0000 p0002
      p0006
  exact p0007

@[expose]
noncomputable def g_opelcnv (A : Class) (B : Class) (R : Class) :
    Nominal.NPrf
      (syn_wb (.classMem (syn_cop A B) (syn_ccnv R)) (.classMem (syn_cop B A) R)) :=
  by
  have p0000 := @g_brcnv A B R
  have p0001 := (Nominal.biimpRefl (syn_wbr A (syn_ccnv R) B))
  have p0002 := (Nominal.biimpRefl (syn_wbr B R A))
  have p0003 :=
    @g_n_3bitr3i (syn_wbr A (syn_ccnv R) B) (syn_wbr B R A)
      (.classMem (syn_cop A B) (syn_ccnv R)) (.classMem (syn_cop B A) R) p0000 p0001 p0002
  exact p0003

@[expose]
noncomputable def g_cnvco (A : Class) (B : Class) :
    Nominal.NPrf
      (.classEq (syn_ccnv (syn_ccom A B)) (syn_ccom (syn_ccnv B) (syn_ccnv A))) :=
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
  have dv_cache_0005 : y ∉ ((syn_ccom A B)).fv :=
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
  have dv_cache_0006 : x ∉ ((syn_ccom A B)).fv :=
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
  have dv_cache_0008 : y ∉ ((syn_ccnv B)).fv :=
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
  have dv_cache_0009 : x ∉ ((syn_ccnv B)).fv :=
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
  have dv_cache_0010 : z ∉ ((syn_ccnv B)).fv :=
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
  have dv_cache_0011 : y ∉ ((syn_ccnv A)).fv :=
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
  have dv_cache_0012 : x ∉ ((syn_ccnv A)).fv :=
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
  have dv_cache_0013 : z ∉ ((syn_ccnv A)).fv :=
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
    @g_brco z (.cv x) (.cv y) A B dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0001 := @g_brcnv (.cv z) (.cv x) B
  have p0002 := @g_brcnv (.cv y) (.cv z) A
  have p0003 :=
    @g_anbi12i (syn_wbr (.cv z) (syn_ccnv B) (.cv x)) (syn_wbr (.cv x) B (.cv z))
      (syn_wbr (.cv y) (syn_ccnv A) (.cv z)) (syn_wbr (.cv z) A (.cv y)) p0001 p0002
  have p0004 :=
    @g_ancom (syn_wbr (.cv z) (syn_ccnv B) (.cv x)) (syn_wbr (.cv y) (syn_ccnv A) (.cv z))
  have p0005 :=
    @g_bitr3i (syn_wa (syn_wbr (.cv x) B (.cv z)) (syn_wbr (.cv z) A (.cv y)))
      (syn_wa (syn_wbr (.cv z) (syn_ccnv B) (.cv x)) (syn_wbr (.cv y) (syn_ccnv A) (.cv z)))
      (syn_wa (syn_wbr (.cv y) (syn_ccnv A) (.cv z)) (syn_wbr (.cv z) (syn_ccnv B) (.cv x)))
      p0003 p0004
  have p0006 :=
    @g_exbii (syn_wa (syn_wbr (.cv x) B (.cv z)) (syn_wbr (.cv z) A (.cv y)))
      (syn_wa (syn_wbr (.cv y) (syn_ccnv A) (.cv z)) (syn_wbr (.cv z) (syn_ccnv B) (.cv x)))
      z p0005
  have p0007 :=
    @g_bitri (syn_wbr (.cv x) (syn_ccom A B) (.cv y))
      (syn_wex z (syn_wa (syn_wbr (.cv x) B (.cv z)) (syn_wbr (.cv z) A (.cv y))))
      (syn_wex z (syn_wa (syn_wbr (.cv y) (syn_ccnv A) (.cv z))
          (syn_wbr (.cv z) (syn_ccnv B) (.cv x))))
      p0000 p0006
  have p0008 :=
    @g_opabbii (syn_wbr (.cv x) (syn_ccom A B) (.cv y))
      (syn_wex z (syn_wa (syn_wbr (.cv y) (syn_ccnv A) (.cv z))
          (syn_wbr (.cv z) (syn_ccnv B) (.cv x))))
      y x p0007
  have p0009 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_cnv y x
      (syn_ccom A B) dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0010 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_co y x z
      (syn_ccnv B) (syn_ccnv A) dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0007 dv_cache_0014 dv_cache_0015
  have p0011 :=
    @g_n_3eqtr4i (syn_copab y x (syn_wbr (.cv x) (syn_ccom A B) (.cv y)))
      (syn_copab y x (syn_wex z (syn_wa (syn_wbr (.cv y) (syn_ccnv A) (.cv z))
            (syn_wbr (.cv z) (syn_ccnv B) (.cv x)))))
      (syn_ccnv (syn_ccom A B)) (syn_ccom (syn_ccnv B) (syn_ccnv A)) p0008 p0009 p0010
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

@[expose]
noncomputable def g_cnvuni (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (.classEq (syn_ccnv (syn_cuni A)) (syn_ciun x A (syn_ccnv (.cv x)))) :=
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
  have dv_cache_0003 : z ∉ ((syn_cuni A)).fv :=
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
  have dv_cache_0004 : w ∉ ((syn_cuni A)).fv :=
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
  have dv_cache_0006 : x ∉ ((syn_cop (.cv w) (.cv z))).fv :=
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
  have dv_cache_0008 : x ∉ ((Wff.classEq (.cv y) (syn_cop (.cv z) (.cv w)))).fv :=
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
  have dv_cache_0016 : y ∉ ((syn_ccnv (syn_cuni A))).fv :=
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
  have dv_cache_0017 : y ∉ ((syn_ciun x A (syn_ccnv (.cv x)))).fv :=
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
    @g_elcnv2 z w (.cv y) (syn_cuni A) dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005
  have p0001 := @g_eluni2 x (syn_cop (.cv w) (.cv z)) A dv_cache_0006 dv_cache_0007
  have p0002 :=
    @g_anbi2i (.classMem (syn_cop (.cv w) (.cv z)) (syn_cuni A))
      (syn_wrex x A (.classMem (syn_cop (.cv w) (.cv z)) (.cv x)))
      (.classEq (.cv y) (syn_cop (.cv z) (.cv w))) p0001
  have p0003 :=
    @g_r19_42v (.classEq (.cv y) (syn_cop (.cv z) (.cv w)))
      (.classMem (syn_cop (.cv w) (.cv z)) (.cv x)) x A dv_cache_0008
  have p0004 :=
    @g_bitr4i
      (syn_wa (.classEq (.cv y) (syn_cop (.cv z) (.cv w)))
        (.classMem (syn_cop (.cv w) (.cv z)) (syn_cuni A)))
      (syn_wa (.classEq (.cv y) (syn_cop (.cv z) (.cv w)))
        (syn_wrex x A (.classMem (syn_cop (.cv w) (.cv z)) (.cv x))))
      (syn_wrex x A (syn_wa (.classEq (.cv y) (syn_cop (.cv z) (.cv w)))
          (.classMem (syn_cop (.cv w) (.cv z)) (.cv x))))
      p0002 p0003
  have p0005 :=
    @g_n_2exbii
      (syn_wa (.classEq (.cv y) (syn_cop (.cv z) (.cv w)))
        (.classMem (syn_cop (.cv w) (.cv z)) (syn_cuni A)))
      (syn_wrex x A (syn_wa (.classEq (.cv y) (syn_cop (.cv z) (.cv w)))
          (.classMem (syn_cop (.cv w) (.cv z)) (.cv x))))
      z w p0004
  have p0006 :=
    @g_elcnv2 z w (.cv y) (.cv x) dv_cache_0001 dv_cache_0002 dv_cache_0009 dv_cache_0010
      dv_cache_0005
  have p0007 :=
    @g_rexbii (.classMem (.cv y) (syn_ccnv (.cv x)))
      (syn_wex z (syn_wex w (syn_wa (.classEq (.cv y) (syn_cop (.cv z) (.cv w)))
            (.classMem (syn_cop (.cv w) (.cv z)) (.cv x)))))
      x A p0006
  have p0008 :=
    @g_rexcom4
      (syn_wex w (syn_wa (.classEq (.cv y) (syn_cop (.cv z) (.cv w)))
          (.classMem (syn_cop (.cv w) (.cv z)) (.cv x))))
      x z A dv_cache_0011 dv_cache_0012
  have p0009 :=
    @g_rexcom4
      (syn_wa (.classEq (.cv y) (syn_cop (.cv z) (.cv w)))
        (.classMem (syn_cop (.cv w) (.cv z)) (.cv x)))
      x w A dv_cache_0013 dv_cache_0014
  have p0010 :=
    @g_exbii
      (syn_wrex x A (syn_wex w (syn_wa (.classEq (.cv y) (syn_cop (.cv z) (.cv w)))
            (.classMem (syn_cop (.cv w) (.cv z)) (.cv x)))))
      (syn_wex w (syn_wrex x A (syn_wa (.classEq (.cv y) (syn_cop (.cv z) (.cv w)))
            (.classMem (syn_cop (.cv w) (.cv z)) (.cv x)))))
      z p0009
  have p0011 :=
    @g_n_3bitrri (syn_wrex x A (.classMem (.cv y) (syn_ccnv (.cv x))))
      (syn_wrex x A (syn_wex z (syn_wex w (syn_wa (.classEq (.cv y) (syn_cop (.cv z) (.cv w)))
              (.classMem (syn_cop (.cv w) (.cv z)) (.cv x))))))
      (syn_wex z (syn_wrex x A (syn_wex w (syn_wa (.classEq (.cv y) (syn_cop (.cv z) (.cv w)))
              (.classMem (syn_cop (.cv w) (.cv z)) (.cv x))))))
      (syn_wex z (syn_wex w (syn_wrex x A (syn_wa (.classEq (.cv y) (syn_cop (.cv z) (.cv w)))
              (.classMem (syn_cop (.cv w) (.cv z)) (.cv x))))))
      p0007 p0008 p0010
  have p0012 :=
    @g_n_3bitri (.classMem (.cv y) (syn_ccnv (syn_cuni A)))
      (syn_wex z (syn_wex w (syn_wa (.classEq (.cv y) (syn_cop (.cv z) (.cv w)))
            (.classMem (syn_cop (.cv w) (.cv z)) (syn_cuni A)))))
      (syn_wex z (syn_wex w (syn_wrex x A (syn_wa (.classEq (.cv y) (syn_cop (.cv z) (.cv w)))
              (.classMem (syn_cop (.cv w) (.cv z)) (.cv x))))))
      (syn_wrex x A (.classMem (.cv y) (syn_ccnv (.cv x)))) p0000 p0005 p0011
  have p0013 := @g_eliun x (.cv y) A (syn_ccnv (.cv x)) dv_cache_0015
  have p0014 :=
    @g_bitr4i (.classMem (.cv y) (syn_ccnv (syn_cuni A)))
      (syn_wrex x A (.classMem (.cv y) (syn_ccnv (.cv x))))
      (.classMem (.cv y) (syn_ciun x A (syn_ccnv (.cv x)))) p0012 p0013
  have p0015 :=
    @g_eqriv y (syn_ccnv (syn_cuni A)) (syn_ciun x A (syn_ccnv (.cv x))) dv_cache_0016
      dv_cache_0017 p0014
  exact p0015

@[expose]
noncomputable def g_elrn (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf (syn_wb (.classMem A (syn_crn B)) (syn_wex x (syn_wbr (.cv x) B A))) :=
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
  have dv_cache_0003 : x ∉ ((syn_cvv)).fv :=
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
  have p0000 := (Nominal.classEqRefl (syn_crn B))
  have p0001 := @g_eleq2i (syn_crn B) (syn_cima B (syn_cvv)) A p0000
  have p0002 := @g_elima x A B (syn_cvv) dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0003 := @g_rexv (syn_wbr (.cv x) B A) x
  have p0004 :=
    @g_n_3bitri (.classMem A (syn_crn B)) (.classMem A (syn_cima B (syn_cvv)))
      (syn_wrex x (syn_cvv) (syn_wbr (.cv x) B A)) (syn_wex x (syn_wbr (.cv x) B A)) p0001
      p0002 p0003
  exact p0004

@[expose]
noncomputable def g_elrn2 (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf
      (syn_wb (.classMem A (syn_crn B)) (syn_wex x (.classMem (syn_cop (.cv x) A) B))) :=
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
  have p0000 := @g_elrn x A B dv_cache_0001 dv_cache_0002
  have p0001 := (Nominal.biimpRefl (syn_wbr (.cv x) B A))
  have p0002 := @g_exbii (syn_wbr (.cv x) B A) (.classMem (syn_cop (.cv x) A) B) x p0001
  have p0003 :=
    @g_bitri (.classMem A (syn_crn B)) (syn_wex x (syn_wbr (.cv x) B A))
      (syn_wex x (.classMem (syn_cop (.cv x) A) B)) p0000 p0002
  exact p0003

@[expose]
noncomputable def g_eldm (y : Var) (A : Class) (B : Class) (dv_A_y : y ∉ A.fv)
    (dv_B_y : y ∉ B.fv) :
    Nominal.NPrf (syn_wb (.classMem A (syn_cdm B)) (syn_wex y (syn_wbr A B (.cv y)))) :=
  by
  have dv_cache_0001 : y ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_y, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_ccnv B)).fv :=
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
  have p0000 := (Nominal.classEqRefl (syn_cdm B))
  have p0001 := @g_eleq2i (syn_cdm B) (syn_crn (syn_ccnv B)) A p0000
  have p0002 := @g_elrn y A (syn_ccnv B) dv_cache_0001 dv_cache_0002
  have p0003 :=
    @g_bitri (.classMem A (syn_cdm B)) (.classMem A (syn_crn (syn_ccnv B)))
      (syn_wex y (syn_wbr (.cv y) (syn_ccnv B) A)) p0001 p0002
  have p0004 := @g_brcnv (.cv y) A B
  have p0005 := @g_exbii (syn_wbr (.cv y) (syn_ccnv B) A) (syn_wbr A B (.cv y)) y p0004
  have p0006 :=
    @g_bitri (.classMem A (syn_cdm B)) (syn_wex y (syn_wbr (.cv y) (syn_ccnv B) A))
      (syn_wex y (syn_wbr A B (.cv y))) p0003 p0005
  exact p0006

@[expose]
noncomputable def g_eldm2 (y : Var) (A : Class) (B : Class) (dv_A_y : y ∉ A.fv)
    (dv_B_y : y ∉ B.fv) :
    Nominal.NPrf
      (syn_wb (.classMem A (syn_cdm B)) (syn_wex y (.classMem (syn_cop A (.cv y)) B))) :=
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
  have p0000 := @g_eldm y A B dv_cache_0001 dv_cache_0002
  have p0001 := (Nominal.biimpRefl (syn_wbr A B (.cv y)))
  have p0002 := @g_exbii (syn_wbr A B (.cv y)) (.classMem (syn_cop A (.cv y)) B) y p0001
  have p0003 :=
    @g_bitri (.classMem A (syn_cdm B)) (syn_wex y (syn_wbr A B (.cv y)))
      (syn_wex y (.classMem (syn_cop A (.cv y)) B)) p0000 p0002
  exact p0003

@[expose]
noncomputable def g_dfdm2 (x : Var) (y : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.classEq (syn_cdm A) (.cab x (syn_wex y (syn_wbr (.cv x) A (.cv y))))) :=
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
  have dv_cache_0003 : x ∉ ((syn_cdm A)).fv :=
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
  have p0000 := @g_eldm y (.cv x) A dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_eqabi (syn_wex y (syn_wbr (.cv x) A (.cv y))) x (syn_cdm A) dv_cache_0003 p0000
  exact p0001

@[expose]
noncomputable def g_dfdm3 (x : Var) (y : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.classEq (syn_cdm A) (.cab x (syn_wex y (.classMem (syn_cop (.cv x) (.cv y)) A)))) :=
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
  have dv_cache_0003 : x ∉ ((syn_cdm A)).fv :=
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
  have p0000 := @g_eldm2 y (.cv x) A dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_eqabi (syn_wex y (.classMem (syn_cop (.cv x) (.cv y)) A)) x (syn_cdm A)
      dv_cache_0003 p0000
  exact p0001

@[expose]
noncomputable def g_dfrn2 (x : Var) (y : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.classEq (syn_crn A) (.cab y (syn_wex x (syn_wbr (.cv x) A (.cv y))))) :=
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
  have dv_cache_0003 : y ∉ ((syn_crn A)).fv :=
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
  have p0000 := @g_elrn x (.cv y) A dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_eqabi (syn_wex x (syn_wbr (.cv x) A (.cv y))) y (syn_crn A) dv_cache_0003 p0000
  exact p0001

@[expose]
noncomputable def g_dfrn3 (x : Var) (y : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.classEq (syn_crn A) (.cab y (syn_wex x (.classMem (syn_cop (.cv x) (.cv y)) A)))) :=
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
  have p0000 := @g_dfrn2 x y A dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 := (Nominal.biimpRefl (syn_wbr (.cv x) A (.cv y)))
  have p0002 :=
    @g_exbii (syn_wbr (.cv x) A (.cv y)) (.classMem (syn_cop (.cv x) (.cv y)) A) x p0001
  have p0003 :=
    @g_abbii (syn_wex x (syn_wbr (.cv x) A (.cv y)))
      (syn_wex x (.classMem (syn_cop (.cv x) (.cv y)) A)) y p0002
  have p0004 :=
    @g_eqtri (syn_crn A) (.cab y (syn_wex x (syn_wbr (.cv x) A (.cv y))))
      (.cab y (syn_wex x (.classMem (syn_cop (.cv x) (.cv y)) A))) p0000 p0003
  exact p0004

@[expose]
noncomputable def g_dfrn4 (A : Class) :
    Nominal.NPrf (.classEq (syn_crn A) (syn_cdm (syn_ccnv A))) :=
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
  have dv_cache_0002 : y ∉ ((syn_ccnv A)).fv :=
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
  have dv_cache_0004 : x ∉ ((syn_crn A)).fv :=
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
  have dv_cache_0005 : x ∉ ((syn_cdm (syn_ccnv A))).fv :=
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
  have p0000 := @g_brcnv (.cv x) (.cv y) A
  have p0001 :=
    @g_exbii (syn_wbr (.cv x) (syn_ccnv A) (.cv y)) (syn_wbr (.cv y) A (.cv x)) y p0000
  have p0002 := @g_eldm y (.cv x) (syn_ccnv A) dv_cache_0001 dv_cache_0002
  have p0003 := @g_elrn y (.cv x) A dv_cache_0001 dv_cache_0003
  have p0004 :=
    @g_n_3bitr4ri (syn_wex y (syn_wbr (.cv x) (syn_ccnv A) (.cv y)))
      (syn_wex y (syn_wbr (.cv y) A (.cv x))) (.classMem (.cv x) (syn_cdm (syn_ccnv A)))
      (.classMem (.cv x) (syn_crn A)) p0001 p0002 p0003
  have p0005 :=
    @g_eqriv x (syn_crn A) (syn_cdm (syn_ccnv A)) dv_cache_0004 dv_cache_0005 p0004
  exact p0005

@[expose]
noncomputable def g_dfdmf (x : Var) (y : Var) (A : Class) (dv_x_y : x ≠ y)
    (hyp_dfdmf_1 : Nominal.NPrf (syn_wnfc x A))
    (hyp_dfdmf_2 : Nominal.NPrf (syn_wnfc y A)) :
    Nominal.NPrf
      (.classEq (syn_cdm A) (.cab x (syn_wex y (syn_wbr (.cv x) A (.cv y))))) :=
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
  have dv_cache_0006 : v ∉ ((syn_wbr (.cv w) A (.cv y))).fv :=
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
  have dv_cache_0009 : w ∉ ((syn_wex y (syn_wbr (.cv x) A (.cv y)))).fv :=
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
  have p0000 := @g_dfdm2 w v A dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 := @g_nfcv y (.cv w) dv_cache_0004
  have p0002 := @g_nfcv y (.cv v) dv_cache_0005
  have p0003 := @g_nfbr y (.cv w) (.cv v) A p0001 hyp_dfdmf_2 p0002
  have p0004 := @g_nfv (syn_wbr (.cv w) A (.cv y)) v dv_cache_0006
  have p0005 := @g_breq2 (.cv v) (.cv y) (.cv w) A
  have p0006_e02_recanon :
    Nominal.NPrf
      (.imp (.objEq v y) (syn_wb (syn_wbr (.cv w) A (.cv v)) (syn_wbr (.cv w) A (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex
          syn_wex syn_cphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0005
  have p0006 :=
    @g_cbvex (syn_wbr (.cv w) A (.cv v)) (syn_wbr (.cv w) A (.cv y)) v y p0003 p0004
      p0006_e02_recanon
  have p0007 :=
    @g_abbii (syn_wex v (syn_wbr (.cv w) A (.cv v)))
      (syn_wex y (syn_wbr (.cv w) A (.cv y))) w p0006
  have p0008 := @g_nfcv x (.cv w) dv_cache_0007
  have p0009 := @g_nfcv x (.cv y) dv_cache_0008
  have p0010 := @g_nfbr x (.cv w) (.cv y) A p0008 hyp_dfdmf_1 p0009
  have p0011 := @g_nfex (syn_wbr (.cv w) A (.cv y)) x y p0010
  have p0012 := @g_nfv (syn_wex y (syn_wbr (.cv x) A (.cv y))) w dv_cache_0009
  have p0013 := @g_breq1 (.cv w) (.cv x) (.cv y) A
  have p0014_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq w x) (syn_wb (syn_wbr (.cv w) A (.cv y)) (syn_wbr (.cv x) A (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex
          syn_wex syn_cphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0013
  have p0014 :=
    @g_exbidv (.objEq w x) (syn_wbr (.cv w) A (.cv y)) (syn_wbr (.cv x) A (.cv y)) y
      dv_cache_0010 p0014_e00_recanon
  have p0015 :=
    @g_cbvab (syn_wex y (syn_wbr (.cv w) A (.cv y)))
      (syn_wex y (syn_wbr (.cv x) A (.cv y))) w x p0011 p0012 p0014
  have p0016 :=
    @g_n_3eqtri (syn_cdm A) (.cab w (syn_wex v (syn_wbr (.cv w) A (.cv v))))
      (.cab w (syn_wex y (syn_wbr (.cv w) A (.cv y))))
      (.cab x (syn_wex y (syn_wbr (.cv x) A (.cv y)))) p0000 p0007 p0015
  exact p0016

@[expose]
noncomputable def g_dmss (A : Class) (B : Class) :
    Nominal.NPrf (.imp (syn_wss A B) (syn_wss (syn_cdm A) (syn_cdm B))) :=
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
  have dv_cache_0001 : y ∉ ((syn_wss A B)).fv := by
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
  have dv_cache_0005 : x ∉ ((syn_cdm A)).fv :=
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
  have dv_cache_0006 : x ∉ ((syn_cdm B)).fv :=
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
  have dv_cache_0007 : x ∉ ((syn_wss A B)).fv :=
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
  have p0000 := @g_ssel A B (syn_cop (.cv x) (.cv y))
  have p0001 :=
    @g_eximdv (syn_wss A B) (.classMem (syn_cop (.cv x) (.cv y)) A)
      (.classMem (syn_cop (.cv x) (.cv y)) B) y dv_cache_0001 p0000
  have p0002 := @g_eldm2 y (.cv x) A dv_cache_0002 dv_cache_0003
  have p0003 := @g_eldm2 y (.cv x) B dv_cache_0002 dv_cache_0004
  have p0004 :=
    @g_n_3imtr4g (syn_wss A B) (syn_wex y (.classMem (syn_cop (.cv x) (.cv y)) A))
      (syn_wex y (.classMem (syn_cop (.cv x) (.cv y)) B)) (.classMem (.cv x) (syn_cdm A))
      (.classMem (.cv x) (syn_cdm B)) p0001 p0002 p0003
  have p0005 :=
    @g_ssrdv (syn_wss A B) x (syn_cdm A) (syn_cdm B) dv_cache_0005 dv_cache_0006
      dv_cache_0007 p0004
  exact p0005

@[expose]
noncomputable def g_dmeq (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_cdm A) (syn_cdm B))) :=
  by
  have p0000 := @g_dmss A B
  have p0001 := @g_dmss B A
  have p0002 :=
    @g_anim12i (syn_wss A B) (syn_wss (syn_cdm A) (syn_cdm B)) (syn_wss B A)
      (syn_wss (syn_cdm B) (syn_cdm A)) p0000 p0001
  have p0003 := @g_eqss A B
  have p0004 := @g_eqss (syn_cdm A) (syn_cdm B)
  have p0005 :=
    @g_n_3imtr4i (syn_wa (syn_wss A B) (syn_wss B A))
      (syn_wa (syn_wss (syn_cdm A) (syn_cdm B)) (syn_wss (syn_cdm B) (syn_cdm A)))
      (.classEq A B) (.classEq (syn_cdm A) (syn_cdm B)) p0002 p0003 p0004
  exact p0005

@[expose]
noncomputable def g_dmeqi (A : Class) (B : Class)
    (hyp_dmeqi_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (.classEq (syn_cdm A) (syn_cdm B)) :=
  by
  have p0000 := @g_dmeq A B
  have p0001 := Nominal.mp hyp_dmeqi_1 p0000
  exact p0001

@[expose]
noncomputable def g_dmeqd (ph : Wff) (A : Class) (B : Class)
    (hyp_dmeqd_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (syn_cdm A) (syn_cdm B))) :=
  by
  have p0000 := @g_dmeq A B
  have p0001 :=
    @g_syl ph (.classEq A B) (.classEq (syn_cdm A) (syn_cdm B)) hyp_dmeqd_1 p0000
  exact p0001

@[expose]
noncomputable def g_opeldm (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classMem (syn_cop A B) C) (.classMem A (syn_cdm C))) :=
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
  have dv_cache_0002 : y ∉ ((Wff.classMem (syn_cop A B) C)).fv :=
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
  have p0000 := @g_elex (syn_cop A B) C
  have p0001 := @g_opexb A B
  have p0002 :=
    @g_simprbi (.classMem (syn_cop A B) (syn_cvv)) (.classMem A (syn_cvv))
      (.classMem B (syn_cvv)) p0001
  have p0003 :=
    @g_syl (.classMem (syn_cop A B) C) (.classMem (syn_cop A B) (syn_cvv))
      (.classMem B (syn_cvv)) p0000 p0002
  have p0004 := @g_opeq2 (.cv y) B A
  have p0005 := @g_eleq1d (.classEq (.cv y) B) (syn_cop A (.cv y)) (syn_cop A B) C p0004
  have p0006 :=
    @g_spcegv (.classMem (syn_cop A (.cv y)) C) (.classMem (syn_cop A B) C) y B (syn_cvv)
      dv_cache_0001 dv_cache_0002 p0005
  have p0007 :=
    @g_mpcom (.classMem B (syn_cvv)) (.classMem (syn_cop A B) C)
      (syn_wex y (.classMem (syn_cop A (.cv y)) C)) p0003 p0006
  have p0008 := @g_eldm2 y A C dv_cache_0003 dv_cache_0004
  have p0009 :=
    @g_sylibr (.classMem (syn_cop A B) C) (syn_wex y (.classMem (syn_cop A (.cv y)) C))
      (.classMem A (syn_cdm C)) p0007 p0008
  exact p0009

@[expose]
noncomputable def g_breldm (A : Class) (B : Class) (R : Class) :
    Nominal.NPrf (.imp (syn_wbr A R B) (.classMem A (syn_cdm R))) :=
  by
  have p0000 := (Nominal.biimpRefl (syn_wbr A R B))
  have p0001 := @g_opeldm A B R
  have p0002 :=
    @g_sylbi (syn_wbr A R B) (.classMem (syn_cop A B) R) (.classMem A (syn_cdm R)) p0000
      p0001
  exact p0002

@[expose]
noncomputable def g_dmun (A : Class) (B : Class) :
    Nominal.NPrf (.classEq (syn_cdm (syn_cun A B)) (syn_cun (syn_cdm A) (syn_cdm B))) :=
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
  have dv_cache_0001 : x ∉ ((syn_cun A B)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_cun A B)).fv :=
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
  have dv_cache_0007 : x ∉ ((syn_cun (syn_cdm A) (syn_cdm B))).fv :=
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
  have p0000 := @g_dfdm3 x y (syn_cun A B) dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 := @g_eldm y (.cv x) A dv_cache_0004 dv_cache_0005
  have p0002 := @g_eldm y (.cv x) B dv_cache_0004 dv_cache_0006
  have p0003 :=
    @g_orbi12i (.classMem (.cv x) (syn_cdm A)) (syn_wex y (syn_wbr (.cv x) A (.cv y)))
      (.classMem (.cv x) (syn_cdm B)) (syn_wex y (syn_wbr (.cv x) B (.cv y))) p0001 p0002
  have p0004 := @g_elun (.cv x) (syn_cdm A) (syn_cdm B)
  have p0005 := (Nominal.biimpRefl (syn_wbr (.cv x) (syn_cun A B) (.cv y)))
  have p0006 := @g_brun (.cv x) (.cv y) A B
  have p0007 :=
    @g_bitr3i (.classMem (syn_cop (.cv x) (.cv y)) (syn_cun A B))
      (syn_wbr (.cv x) (syn_cun A B) (.cv y))
      (syn_wo (syn_wbr (.cv x) A (.cv y)) (syn_wbr (.cv x) B (.cv y))) p0005 p0006
  have p0008 :=
    @g_exbii (.classMem (syn_cop (.cv x) (.cv y)) (syn_cun A B))
      (syn_wo (syn_wbr (.cv x) A (.cv y)) (syn_wbr (.cv x) B (.cv y))) y p0007
  have p0009 := @g_n_19_43 (syn_wbr (.cv x) A (.cv y)) (syn_wbr (.cv x) B (.cv y)) y
  have p0010 :=
    @g_bitri (syn_wex y (.classMem (syn_cop (.cv x) (.cv y)) (syn_cun A B)))
      (syn_wex y (syn_wo (syn_wbr (.cv x) A (.cv y)) (syn_wbr (.cv x) B (.cv y))))
      (syn_wo (syn_wex y (syn_wbr (.cv x) A (.cv y))) (syn_wex y (syn_wbr (.cv x) B (.cv y))))
      p0008 p0009
  have p0011 :=
    @g_n_3bitr4i (syn_wo (.classMem (.cv x) (syn_cdm A)) (.classMem (.cv x) (syn_cdm B)))
      (syn_wo (syn_wex y (syn_wbr (.cv x) A (.cv y))) (syn_wex y (syn_wbr (.cv x) B (.cv y))))
      (.classMem (.cv x) (syn_cun (syn_cdm A) (syn_cdm B)))
      (syn_wex y (.classMem (syn_cop (.cv x) (.cv y)) (syn_cun A B))) p0003 p0004 p0010
  have p0012 :=
    @g_eqabi (syn_wex y (.classMem (syn_cop (.cv x) (.cv y)) (syn_cun A B))) x
      (syn_cun (syn_cdm A) (syn_cdm B)) dv_cache_0007 p0011
  have p0013 :=
    @g_eqtr4i (syn_cdm (syn_cun A B))
      (.cab x (syn_wex y (.classMem (syn_cop (.cv x) (.cv y)) (syn_cun A B))))
      (syn_cun (syn_cdm A) (syn_cdm B)) p0000 p0012
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

@[expose]
noncomputable def g_dmuni (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (.classEq (syn_cdm (syn_cuni A)) (syn_ciun x A (syn_cdm (.cv x)))) :=
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
  have dv_cache_0001 : x ∉ ((syn_cop (.cv y) (.cv z))).fv := by
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
  have dv_cache_0006 : z ∉ ((syn_cuni A)).fv :=
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
  have dv_cache_0008 : y ∉ ((syn_cdm (syn_cuni A))).fv :=
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
  have dv_cache_0009 : y ∉ ((syn_ciun x A (syn_cdm (.cv x)))).fv :=
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
  have p0000 := @g_eluni x (syn_cop (.cv y) (.cv z)) A dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_exbii (.classMem (syn_cop (.cv y) (.cv z)) (syn_cuni A))
      (syn_wex x (syn_wa (.classMem (syn_cop (.cv y) (.cv z)) (.cv x)) (.classMem (.cv x) A)))
      z p0000
  have p0002 :=
    @g_excom (syn_wa (.classMem (syn_cop (.cv y) (.cv z)) (.cv x)) (.classMem (.cv x) A))
      z x
  have p0003 :=
    @g_n_19_41v (.classMem (syn_cop (.cv y) (.cv z)) (.cv x)) (.classMem (.cv x) A) z
      dv_cache_0003
  have p0004 := @g_ancom (.classMem (.cv x) A) (.classMem (.cv y) (syn_cdm (.cv x)))
  have p0005 := @g_eldm2 z (.cv y) (.cv x) dv_cache_0004 dv_cache_0005
  have p0006 :=
    @g_anbi1i (.classMem (.cv y) (syn_cdm (.cv x)))
      (syn_wex z (.classMem (syn_cop (.cv y) (.cv z)) (.cv x))) (.classMem (.cv x) A)
      p0005
  have p0007 :=
    @g_bitri (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) (syn_cdm (.cv x))))
      (syn_wa (.classMem (.cv y) (syn_cdm (.cv x))) (.classMem (.cv x) A))
      (syn_wa (syn_wex z (.classMem (syn_cop (.cv y) (.cv z)) (.cv x))) (.classMem (.cv x) A))
      p0004 p0006
  have p0008 :=
    @g_bicomi (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) (syn_cdm (.cv x))))
      (syn_wa (syn_wex z (.classMem (syn_cop (.cv y) (.cv z)) (.cv x))) (.classMem (.cv x) A))
      p0007
  have p0009 :=
    @g_bitri
      (syn_wex z (syn_wa (.classMem (syn_cop (.cv y) (.cv z)) (.cv x)) (.classMem (.cv x) A)))
      (syn_wa (syn_wex z (.classMem (syn_cop (.cv y) (.cv z)) (.cv x))) (.classMem (.cv x) A))
      (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) (syn_cdm (.cv x)))) p0003 p0008
  have p0010 :=
    @g_exbii
      (syn_wex z (syn_wa (.classMem (syn_cop (.cv y) (.cv z)) (.cv x)) (.classMem (.cv x) A)))
      (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) (syn_cdm (.cv x)))) x p0009
  have p0011 :=
    @g_n_3bitri (syn_wex z (.classMem (syn_cop (.cv y) (.cv z)) (syn_cuni A)))
      (syn_wex z (syn_wex x
          (syn_wa (.classMem (syn_cop (.cv y) (.cv z)) (.cv x)) (.classMem (.cv x) A))))
      (syn_wex x (syn_wex z
          (syn_wa (.classMem (syn_cop (.cv y) (.cv z)) (.cv x)) (.classMem (.cv x) A))))
      (syn_wex x (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) (syn_cdm (.cv x)))))
      p0001 p0002 p0010
  have p0012 := (Nominal.biimpRefl (syn_wrex x A (.classMem (.cv y) (syn_cdm (.cv x)))))
  have p0013 :=
    @g_bitr4i (syn_wex z (.classMem (syn_cop (.cv y) (.cv z)) (syn_cuni A)))
      (syn_wex x (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) (syn_cdm (.cv x)))))
      (syn_wrex x A (.classMem (.cv y) (syn_cdm (.cv x)))) p0011 p0012
  have p0014 := @g_eldm2 z (.cv y) (syn_cuni A) dv_cache_0004 dv_cache_0006
  have p0015 := @g_eliun x (.cv y) A (syn_cdm (.cv x)) dv_cache_0007
  have p0016 :=
    @g_n_3bitr4i (syn_wex z (.classMem (syn_cop (.cv y) (.cv z)) (syn_cuni A)))
      (syn_wrex x A (.classMem (.cv y) (syn_cdm (.cv x))))
      (.classMem (.cv y) (syn_cdm (syn_cuni A)))
      (.classMem (.cv y) (syn_ciun x A (syn_cdm (.cv x)))) p0013 p0014 p0015
  have p0017 :=
    @g_eqriv y (syn_cdm (syn_cuni A)) (syn_ciun x A (syn_cdm (.cv x))) dv_cache_0008
      dv_cache_0009 p0016
  exact p0017

@[expose]
noncomputable def g_dmopab (ph : Wff) (x : Var) (y : Var) (dv_x_y : x ≠ y) :
    Nominal.NPrf (.classEq (syn_cdm (syn_copab x y ph)) (.cab x (syn_wex y ph))) :=
  by
  have dv_cache_0001 : x ≠ y := by exact (show x ≠ y from (by exact dv_x_y))
  have p0000 := @g_nfopab1 ph x y
  have p0001 := @g_nfopab2 ph x y
  have p0002 := @g_dfdmf x y (syn_copab x y ph) dv_cache_0001 p0000 p0001
  have p0003 := (Nominal.biimpRefl (syn_wbr (.cv x) (syn_copab x y ph) (.cv y)))
  have p0004 := @g_opabid ph x y
  have p0005 :=
    @g_bitri (syn_wbr (.cv x) (syn_copab x y ph) (.cv y))
      (.classMem (syn_cop (.cv x) (.cv y)) (syn_copab x y ph)) ph p0003 p0004
  have p0006 := @g_exbii (syn_wbr (.cv x) (syn_copab x y ph) (.cv y)) ph y p0005
  have p0007 :=
    @g_abbii (syn_wex y (syn_wbr (.cv x) (syn_copab x y ph) (.cv y))) (syn_wex y ph) x
      p0006
  have p0008 :=
    @g_eqtri (syn_cdm (syn_copab x y ph))
      (.cab x (syn_wex y (syn_wbr (.cv x) (syn_copab x y ph) (.cv y))))
      (.cab x (syn_wex y ph)) p0002 p0007
  exact p0008

@[expose]
noncomputable def g_dmopab3 (ph : Wff) (x : Var) (y : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (syn_wb (syn_wral x A (syn_wex y ph))
        (.classEq (syn_cdm (syn_copab x y (syn_wa (.classMem (.cv x) A) ph))) A)) :=
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
  have p0000 := (Nominal.biimpRefl (syn_wral x A (syn_wex y ph)))
  have p0001 := @g_pm4_71 (.classMem (.cv x) A) (syn_wex y ph)
  have p0002 :=
    @g_albii (.imp (.classMem (.cv x) A) (syn_wex y ph))
      (syn_wb (.classMem (.cv x) A) (syn_wa (.classMem (.cv x) A) (syn_wex y ph))) x p0001
  have p0003 := @g_dmopab (syn_wa (.classMem (.cv x) A) ph) x y dv_cache_0001
  have p0004 := @g_n_19_42v (.classMem (.cv x) A) ph y dv_cache_0002
  have p0005 :=
    @g_abbii (syn_wex y (syn_wa (.classMem (.cv x) A) ph))
      (syn_wa (.classMem (.cv x) A) (syn_wex y ph)) x p0004
  have p0006 :=
    @g_eqtri (syn_cdm (syn_copab x y (syn_wa (.classMem (.cv x) A) ph)))
      (.cab x (syn_wex y (syn_wa (.classMem (.cv x) A) ph)))
      (.cab x (syn_wa (.classMem (.cv x) A) (syn_wex y ph))) p0003 p0005
  have p0007 :=
    @g_eqeq1i (syn_cdm (syn_copab x y (syn_wa (.classMem (.cv x) A) ph)))
      (.cab x (syn_wa (.classMem (.cv x) A) (syn_wex y ph))) A p0006
  have p0008 := @g_eqcom A (.cab x (syn_wa (.classMem (.cv x) A) (syn_wex y ph)))
  have p0009 := @g_eqabb (syn_wa (.classMem (.cv x) A) (syn_wex y ph)) x A dv_cache_0003
  have p0010 :=
    @g_n_3bitr2ri (.classEq (syn_cdm (syn_copab x y (syn_wa (.classMem (.cv x) A) ph))) A)
      (.classEq (.cab x (syn_wa (.classMem (.cv x) A) (syn_wex y ph))) A)
      (.classEq A (.cab x (syn_wa (.classMem (.cv x) A) (syn_wex y ph))))
      (.all x (syn_wb (.classMem (.cv x) A) (syn_wa (.classMem (.cv x) A) (syn_wex y ph))))
      p0007 p0008 p0009
  have p0011 :=
    @g_n_3bitri (syn_wral x A (syn_wex y ph))
      (.all x (.imp (.classMem (.cv x) A) (syn_wex y ph)))
      (.all x (syn_wb (.classMem (.cv x) A) (syn_wa (.classMem (.cv x) A) (syn_wex y ph))))
      (.classEq (syn_cdm (syn_copab x y (syn_wa (.classMem (.cv x) A) ph))) A) p0000 p0002
      p0010
  exact p0011

@[expose]
noncomputable def g_dm0 : Nominal.NPrf (.classEq (syn_cdm (syn_c0)) (syn_c0)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have dv_cache_0001 : x ∉ ((syn_cdm (syn_c0))).fv := by
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
  have dv_cache_0003 : y ∉ ((syn_c0)).fv :=
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
  have p0000 := @g_eq0 x (syn_cdm (syn_c0)) dv_cache_0001
  have p0001 := @g_noel (syn_cop (.cv x) (.cv y))
  have p0002 := @g_nex (.classMem (syn_cop (.cv x) (.cv y)) (syn_c0)) y p0001
  have p0003 := @g_eldm2 y (.cv x) (syn_c0) dv_cache_0002 dv_cache_0003
  have p0004 :=
    @g_mtbir (.classMem (.cv x) (syn_cdm (syn_c0)))
      (syn_wex y (.classMem (syn_cop (.cv x) (.cv y)) (syn_c0))) p0002 p0003
  have p0005 :=
    @g_mpgbir (.classEq (syn_cdm (syn_c0)) (syn_c0))
      (.neg (.classMem (.cv x) (syn_cdm (syn_c0)))) x p0000 p0004
  exact p0005

@[expose]
noncomputable def g_dmi : Nominal.NPrf (.classEq (syn_cdm (syn_cid)) (syn_cvv)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have dv_cache_0001 : x ∉ ((syn_cdm (syn_cid))).fv := by
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
  have dv_cache_0003 : y ∉ ((syn_cid)).fv :=
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
  have p0000 := @g_eqv x (syn_cdm (syn_cid)) dv_cache_0001
  have p0001 := @g_a9e y x
  have p0002 := @g_vex y
  have p0003 := @g_ideq (.cv x) (.cv y) p0002
  have p0004 := @g_equcom x y
  have p0005_e00_recanon :
    Nominal.NPrf (syn_wb (syn_wbr (.cv x) (syn_cid) (.cv y)) (.objEq x y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex
          syn_wex syn_cphi syn_cid syn_copab
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
    @g_bitri (syn_wbr (.cv x) (syn_cid) (.cv y)) (.objEq x y) (.objEq y x)
      p0005_e00_recanon p0004
  have p0006 := @g_exbii (syn_wbr (.cv x) (syn_cid) (.cv y)) (.objEq y x) y p0005
  have p0007 :=
    @g_mpbir (syn_wex y (syn_wbr (.cv x) (syn_cid) (.cv y))) (syn_wex y (.objEq y x))
      p0001 p0006
  have p0008 := @g_eldm y (.cv x) (syn_cid) dv_cache_0002 dv_cache_0003
  have p0009 :=
    @g_mpbir (.classMem (.cv x) (syn_cdm (syn_cid)))
      (syn_wex y (syn_wbr (.cv x) (syn_cid) (.cv y))) p0007 p0008
  have p0010 :=
    @g_mpgbir (.classEq (syn_cdm (syn_cid)) (syn_cvv))
      (.classMem (.cv x) (syn_cdm (syn_cid))) x p0000 p0009
  exact p0010

@[expose]
noncomputable def g_dm0rn0 (A : Class) :
    Nominal.NPrf
      (syn_wb (.classEq (syn_cdm A) (syn_c0)) (.classEq (syn_crn A) (syn_c0))) :=
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
  have dv_cache_0001 : x ∉ ((syn_c0)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_c0)).fv :=
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
  have p0000 := @g_alnex (syn_wex y (syn_wbr (.cv x) A (.cv y))) x
  have p0001 := @g_excom (syn_wbr (.cv x) A (.cv y)) x y
  have p0002 :=
    @g_xchbinx (.all x (.neg (syn_wex y (syn_wbr (.cv x) A (.cv y)))))
      (syn_wex x (syn_wex y (syn_wbr (.cv x) A (.cv y))))
      (syn_wex y (syn_wex x (syn_wbr (.cv x) A (.cv y)))) p0000 p0001
  have p0003 := @g_alnex (syn_wex x (syn_wbr (.cv x) A (.cv y))) y
  have p0004 :=
    @g_bitr4i (.all x (.neg (syn_wex y (syn_wbr (.cv x) A (.cv y)))))
      (.neg (syn_wex y (syn_wex x (syn_wbr (.cv x) A (.cv y)))))
      (.all y (.neg (syn_wex x (syn_wbr (.cv x) A (.cv y))))) p0002 p0003
  have p0005 := @g_noel (.cv x)
  have p0006 :=
    @g_nbn (.classMem (.cv x) (syn_c0)) (syn_wex y (syn_wbr (.cv x) A (.cv y))) p0005
  have p0007 :=
    @g_albii (.neg (syn_wex y (syn_wbr (.cv x) A (.cv y))))
      (syn_wb (syn_wex y (syn_wbr (.cv x) A (.cv y))) (.classMem (.cv x) (syn_c0))) x
      p0006
  have p0008 := @g_noel (.cv y)
  have p0009 :=
    @g_nbn (.classMem (.cv y) (syn_c0)) (syn_wex x (syn_wbr (.cv x) A (.cv y))) p0008
  have p0010 :=
    @g_albii (.neg (syn_wex x (syn_wbr (.cv x) A (.cv y))))
      (syn_wb (syn_wex x (syn_wbr (.cv x) A (.cv y))) (.classMem (.cv y) (syn_c0))) y
      p0009
  have p0011 :=
    @g_n_3bitr3i (.all x (.neg (syn_wex y (syn_wbr (.cv x) A (.cv y)))))
      (.all y (.neg (syn_wex x (syn_wbr (.cv x) A (.cv y)))))
      (.all x (syn_wb (syn_wex y (syn_wbr (.cv x) A (.cv y))) (.classMem (.cv x) (syn_c0))))
      (.all y (syn_wb (syn_wex x (syn_wbr (.cv x) A (.cv y))) (.classMem (.cv y) (syn_c0))))
      p0004 p0007 p0010
  have p0012 := @g_eqabcb (syn_wex y (syn_wbr (.cv x) A (.cv y))) x (syn_c0) dv_cache_0001
  have p0013 := @g_eqabcb (syn_wex x (syn_wbr (.cv x) A (.cv y))) y (syn_c0) dv_cache_0002
  have p0014 :=
    @g_n_3bitr4i
      (.all x (syn_wb (syn_wex y (syn_wbr (.cv x) A (.cv y))) (.classMem (.cv x) (syn_c0))))
      (.all y (syn_wb (syn_wex x (syn_wbr (.cv x) A (.cv y))) (.classMem (.cv y) (syn_c0))))
      (.classEq (.cab x (syn_wex y (syn_wbr (.cv x) A (.cv y)))) (syn_c0))
      (.classEq (.cab y (syn_wex x (syn_wbr (.cv x) A (.cv y)))) (syn_c0)) p0011 p0012
      p0013
  have p0015 := @g_dfdm2 x y A dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0016 :=
    @g_eqeq1i (syn_cdm A) (.cab x (syn_wex y (syn_wbr (.cv x) A (.cv y)))) (syn_c0) p0015
  have p0017 := @g_dfrn2 x y A dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0018 :=
    @g_eqeq1i (syn_crn A) (.cab y (syn_wex x (syn_wbr (.cv x) A (.cv y)))) (syn_c0) p0017
  have p0019 :=
    @g_n_3bitr4i (.classEq (.cab x (syn_wex y (syn_wbr (.cv x) A (.cv y)))) (syn_c0))
      (.classEq (.cab y (syn_wex x (syn_wbr (.cv x) A (.cv y)))) (syn_c0))
      (.classEq (syn_cdm A) (syn_c0)) (.classEq (syn_crn A) (syn_c0)) p0014 p0016 p0018
  exact p0019

@[expose]
noncomputable def g_dmeq0 (A : Class) :
    Nominal.NPrf (syn_wb (.classEq A (syn_c0)) (.classEq (syn_cdm A) (syn_c0))) :=
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
  have dv_cache_0003 : x ∉ ((syn_cdm A)).fv :=
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
  have dv_cache_0005 : x ∉ ((syn_c0)).fv :=
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
  have dv_cache_0006 : y ∉ ((syn_c0)).fv :=
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
  have p0000 := @g_eldm2 y (.cv x) A dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_notbii (.classMem (.cv x) (syn_cdm A))
      (syn_wex y (.classMem (syn_cop (.cv x) (.cv y)) A)) p0000
  have p0002 := @g_alnex (.classMem (syn_cop (.cv x) (.cv y)) A) y
  have p0003 := @g_noel (syn_cop (.cv x) (.cv y))
  have p0004 :=
    @g_nbn (.classMem (syn_cop (.cv x) (.cv y)) (syn_c0))
      (.classMem (syn_cop (.cv x) (.cv y)) A) p0003
  have p0005 :=
    @g_albii (.neg (.classMem (syn_cop (.cv x) (.cv y)) A))
      (syn_wb (.classMem (syn_cop (.cv x) (.cv y)) A)
        (.classMem (syn_cop (.cv x) (.cv y)) (syn_c0)))
      y p0004
  have p0006 :=
    @g_n_3bitr2i (.neg (.classMem (.cv x) (syn_cdm A)))
      (.neg (syn_wex y (.classMem (syn_cop (.cv x) (.cv y)) A)))
      (.all y (.neg (.classMem (syn_cop (.cv x) (.cv y)) A)))
      (.all y (syn_wb (.classMem (syn_cop (.cv x) (.cv y)) A)
          (.classMem (syn_cop (.cv x) (.cv y)) (syn_c0))))
      p0001 p0002 p0005
  have p0007 :=
    @g_albii (.neg (.classMem (.cv x) (syn_cdm A)))
      (.all y (syn_wb (.classMem (syn_cop (.cv x) (.cv y)) A)
          (.classMem (syn_cop (.cv x) (.cv y)) (syn_c0))))
      x p0006
  have p0008 := @g_eq0 x (syn_cdm A) dv_cache_0003
  have p0009 :=
    @g_eqrel x y A (syn_c0) dv_cache_0004 dv_cache_0002 dv_cache_0005 dv_cache_0006
      dv_cache_0007
  have p0010 :=
    @g_n_3bitr4ri (.all x (.neg (.classMem (.cv x) (syn_cdm A))))
      (.all x (.all y (syn_wb (.classMem (syn_cop (.cv x) (.cv y)) A)
            (.classMem (syn_cop (.cv x) (.cv y)) (syn_c0)))))
      (.classEq (syn_cdm A) (syn_c0)) (.classEq A (syn_c0)) p0007 p0008 p0009
  exact p0010

@[expose]
noncomputable def g_dmxp (A : Class) (B : Class) :
    Nominal.NPrf (.imp (syn_wne B (syn_c0)) (.classEq (syn_cdm (syn_cxp A B)) A)) :=
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
  have dv_cache_0006 : y ∉ ((syn_wne B (syn_c0))).fv :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_xp y x A B
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0001 :=
    @g_dmeqi (syn_cxp A B)
      (syn_copab y x (syn_wa (.classMem (.cv y) A) (.classMem (.cv x) B))) p0000
  have p0002 := @g_n0 x B dv_cache_0004
  have p0003 := @g_biimpi (syn_wne B (syn_c0)) (syn_wex x (.classMem (.cv x) B)) p0002
  have p0004 :=
    @g_ralrimivw (syn_wne B (syn_c0)) (syn_wex x (.classMem (.cv x) B)) y A dv_cache_0006
      p0003
  have p0005 :=
    @g_dmopab3 (.classMem (.cv x) B) y x A dv_cache_0001 dv_cache_0002 dv_cache_0005
  have p0006 :=
    @g_sylib (syn_wne B (syn_c0)) (syn_wral y A (syn_wex x (.classMem (.cv x) B)))
      (.classEq
        (syn_cdm (syn_copab y x (syn_wa (.classMem (.cv y) A) (.classMem (.cv x) B)))) A)
      p0004 p0005
  have p0007 :=
    @g_syl5eq (syn_wne B (syn_c0)) (syn_cdm (syn_cxp A B))
      (syn_cdm (syn_copab y x (syn_wa (.classMem (.cv y) A) (.classMem (.cv x) B)))) A
      p0001 p0006
  exact p0007

@[expose]
noncomputable def g_reseq1 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_cres A C) (syn_cres B C))) :=
  by
  have p0000 := @g_ineq1 A B (syn_cxp C (syn_cvv))
  have p0001 := (Nominal.classEqRefl (syn_cres A C))
  have p0002 := (Nominal.classEqRefl (syn_cres B C))
  have p0003 :=
    @g_n_3eqtr4g (.classEq A B) (syn_cin A (syn_cxp C (syn_cvv)))
      (syn_cin B (syn_cxp C (syn_cvv))) (syn_cres A C) (syn_cres B C) p0000 p0001 p0002
  exact p0003

@[expose]
noncomputable def g_reseq2 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_cres C A) (syn_cres C B))) :=
  by
  have p0000 := @g_xpeq1 A B (syn_cvv)
  have p0001 :=
    @g_ineq2d (.classEq A B) (syn_cxp A (syn_cvv)) (syn_cxp B (syn_cvv)) C p0000
  have p0002 := (Nominal.classEqRefl (syn_cres C A))
  have p0003 := (Nominal.classEqRefl (syn_cres C B))
  have p0004 :=
    @g_n_3eqtr4g (.classEq A B) (syn_cin C (syn_cxp A (syn_cvv)))
      (syn_cin C (syn_cxp B (syn_cvv))) (syn_cres C A) (syn_cres C B) p0001 p0002 p0003
  exact p0004

@[expose]
noncomputable def g_reseq1i (A : Class) (B : Class) (C : Class)
    (hyp_reseqi_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (.classEq (syn_cres A C) (syn_cres B C)) :=
  by
  have p0000 := @g_reseq1 A B C
  have p0001 := Nominal.mp hyp_reseqi_1 p0000
  exact p0001

@[expose]
noncomputable def g_reseq2i (A : Class) (B : Class) (C : Class)
    (hyp_reseqi_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (.classEq (syn_cres C A) (syn_cres C B)) :=
  by
  have p0000 := @g_reseq2 A B C
  have p0001 := Nominal.mp hyp_reseqi_1 p0000
  exact p0001

@[expose]
noncomputable def g_reseq12i (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_reseqi_1 : Nominal.NPrf (.classEq A B))
    (hyp_reseqi_2 : Nominal.NPrf (.classEq C D)) :
    Nominal.NPrf (.classEq (syn_cres A C) (syn_cres B D)) :=
  by
  have p0000 := @g_reseq1i A B C hyp_reseqi_1
  have p0001 := @g_reseq2i C D B hyp_reseqi_2
  have p0002 := @g_eqtri (syn_cres A C) (syn_cres B C) (syn_cres B D) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_reseq2d (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_reseqd_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (syn_cres C A) (syn_cres C B))) :=
  by
  have p0000 := @g_reseq2 A B C
  have p0001 :=
    @g_syl ph (.classEq A B) (.classEq (syn_cres C A) (syn_cres C B)) hyp_reseqd_1 p0000
  exact p0001

@[expose]
noncomputable def g_imaeq1 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_cima A C) (syn_cima B C))) :=
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
  have p0000 := @g_breq (.cv y) (.cv x) A B
  have p0001 :=
    @g_rexbidv (.classEq A B) (syn_wbr (.cv y) A (.cv x)) (syn_wbr (.cv y) B (.cv x)) y C
      dv_cache_0001 p0000
  have p0002 :=
    @g_abbidv (.classEq A B) (syn_wrex y C (syn_wbr (.cv y) A (.cv x)))
      (syn_wrex y C (syn_wbr (.cv y) B (.cv x))) x dv_cache_0002 p0001
  have p0003 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_ima x y A C
      dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_ima x y B C
      dv_cache_0008 dv_cache_0009 dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0005 :=
    @g_n_3eqtr4g (.classEq A B) (.cab x (syn_wrex y C (syn_wbr (.cv y) A (.cv x))))
      (.cab x (syn_wrex y C (syn_wbr (.cv y) B (.cv x)))) (syn_cima A C) (syn_cima B C)
      p0002 p0003 p0004
  exact p0005

@[expose]
noncomputable def g_imaeq2 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_cima C A) (syn_cima C B))) :=
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
  have p0000 := @g_rexeq (syn_wbr (.cv y) C (.cv x)) y A B dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_abbidv (.classEq A B) (syn_wrex y A (syn_wbr (.cv y) C (.cv x)))
      (syn_wrex y B (syn_wbr (.cv y) C (.cv x))) x dv_cache_0003 p0000
  have p0002 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_ima x y C A
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0001 dv_cache_0007
  have p0003 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_ima x y C B
      dv_cache_0004 dv_cache_0005 dv_cache_0008 dv_cache_0002 dv_cache_0007
  have p0004 :=
    @g_n_3eqtr4g (.classEq A B) (.cab x (syn_wrex y A (syn_wbr (.cv y) C (.cv x))))
      (.cab x (syn_wrex y B (syn_wbr (.cv y) C (.cv x)))) (syn_cima C A) (syn_cima C B)
      p0001 p0002 p0003
  exact p0004

@[expose]
noncomputable def g_imaeq1i (A : Class) (B : Class) (C : Class)
    (hyp_imaeq1i_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (.classEq (syn_cima A C) (syn_cima B C)) :=
  by
  have p0000 := @g_imaeq1 A B C
  have p0001 := Nominal.mp hyp_imaeq1i_1 p0000
  exact p0001

@[expose]
noncomputable def g_imaeq2i (A : Class) (B : Class) (C : Class)
    (hyp_imaeq1i_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (.classEq (syn_cima C A) (syn_cima C B)) :=
  by
  have p0000 := @g_imaeq2 A B C
  have p0001 := Nominal.mp hyp_imaeq1i_1 p0000
  exact p0001

@[expose]
noncomputable def g_imaeq1d (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_imaeq1d_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (syn_cima A C) (syn_cima B C))) :=
  by
  have p0000 := @g_imaeq1 A B C
  have p0001 :=
    @g_syl ph (.classEq A B) (.classEq (syn_cima A C) (syn_cima B C)) hyp_imaeq1d_1 p0000
  exact p0001

@[expose]
noncomputable def g_imaeq2d (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_imaeq1d_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (syn_cima C A) (syn_cima C B))) :=
  by
  have p0000 := @g_imaeq2 A B C
  have p0001 :=
    @g_syl ph (.classEq A B) (.classEq (syn_cima C A) (syn_cima C B)) hyp_imaeq1d_1 p0000
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

@[expose]
noncomputable def g_elimapw1 (x : Var) (A : Class) (B : Class) (C : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_C_x : x ∉ C.fv) :
    Nominal.NPrf
      (syn_wb (.classMem A (syn_cima B (syn_cpw1 C)))
        (syn_wrex x C (.classMem (syn_cop (syn_csn (.cv x)) A) B))) :=
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
  have dv_cache_0003 : t ∉ ((syn_cpw1 C)).fv :=
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
  have dv_cache_0006 : x ∉ ((syn_wbr (.cv t) B A)).fv :=
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
  have dv_cache_0009 : t ∉ ((syn_csn (.cv x))).fv :=
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
  have dv_cache_0010 : t ∉ ((syn_wbr (syn_csn (.cv x)) B A)).fv :=
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
  have p0000 := @g_elima t A B (syn_cpw1 C) dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 := (Nominal.biimpRefl (syn_wrex t (syn_cpw1 C) (syn_wbr (.cv t) B A)))
  have p0002 := @g_elpw1 x (.cv t) C dv_cache_0004 dv_cache_0005
  have p0003 :=
    @g_anbi1i (.classMem (.cv t) (syn_cpw1 C))
      (syn_wrex x C (.classEq (.cv t) (syn_csn (.cv x)))) (syn_wbr (.cv t) B A) p0002
  have p0004 :=
    @g_r19_41v (.classEq (.cv t) (syn_csn (.cv x))) (syn_wbr (.cv t) B A) x C
      dv_cache_0006
  have p0005 :=
    @g_bitr4i (syn_wa (.classMem (.cv t) (syn_cpw1 C)) (syn_wbr (.cv t) B A))
      (syn_wa (syn_wrex x C (.classEq (.cv t) (syn_csn (.cv x)))) (syn_wbr (.cv t) B A))
      (syn_wrex x C (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (syn_wbr (.cv t) B A)))
      p0003 p0004
  have p0006 :=
    @g_exbii (syn_wa (.classMem (.cv t) (syn_cpw1 C)) (syn_wbr (.cv t) B A))
      (syn_wrex x C (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (syn_wbr (.cv t) B A))) t
      p0005
  have p0007 :=
    @g_rexcom4 (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (syn_wbr (.cv t) B A)) x t C
      dv_cache_0007 dv_cache_0008
  have p0008 :=
    @g_bitr4i (syn_wex t (syn_wa (.classMem (.cv t) (syn_cpw1 C)) (syn_wbr (.cv t) B A)))
      (syn_wex t (syn_wrex x C
          (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (syn_wbr (.cv t) B A))))
      (syn_wrex x C
        (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (syn_wbr (.cv t) B A))))
      p0006 p0007
  have p0009 :=
    @g_bitri (syn_wrex t (syn_cpw1 C) (syn_wbr (.cv t) B A))
      (syn_wex t (syn_wa (.classMem (.cv t) (syn_cpw1 C)) (syn_wbr (.cv t) B A)))
      (syn_wrex x C
        (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (syn_wbr (.cv t) B A))))
      p0001 p0008
  have p0010 := @g_snex (.cv x)
  have p0011 := @g_breq1 (.cv t) (syn_csn (.cv x)) A B
  have p0012 :=
    @g_ceqsexv (syn_wbr (.cv t) B A) (syn_wbr (syn_csn (.cv x)) B A) t (syn_csn (.cv x))
      dv_cache_0009 dv_cache_0010 p0010 p0011
  have p0013 :=
    @g_rexbii
      (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (syn_wbr (.cv t) B A)))
      (syn_wbr (syn_csn (.cv x)) B A) x C p0012
  have p0014 :=
    @g_bitri (syn_wrex t (syn_cpw1 C) (syn_wbr (.cv t) B A))
      (syn_wrex x C
        (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (syn_wbr (.cv t) B A))))
      (syn_wrex x C (syn_wbr (syn_csn (.cv x)) B A)) p0009 p0013
  have p0015 := (Nominal.biimpRefl (syn_wbr (syn_csn (.cv x)) B A))
  have p0016 :=
    @g_rexbii (syn_wbr (syn_csn (.cv x)) B A) (.classMem (syn_cop (syn_csn (.cv x)) A) B)
      x C p0015
  have p0017 :=
    @g_bitri (syn_wrex t (syn_cpw1 C) (syn_wbr (.cv t) B A))
      (syn_wrex x C (syn_wbr (syn_csn (.cv x)) B A))
      (syn_wrex x C (.classMem (syn_cop (syn_csn (.cv x)) A) B)) p0014 p0016
  have p0018 :=
    @g_bitri (.classMem A (syn_cima B (syn_cpw1 C)))
      (syn_wrex t (syn_cpw1 C) (syn_wbr (.cv t) B A))
      (syn_wrex x C (.classMem (syn_cop (syn_csn (.cv x)) A) B)) p0000 p0017
  exact p0018

@[expose]
noncomputable def g_elimapw12 (x : Var) (A : Class) (B : Class) (C : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_C_x : x ∉ C.fv) :
    Nominal.NPrf
      (syn_wb (.classMem A (syn_cima B (syn_cpw1 (syn_cpw1 C))))
        (syn_wrex x C (.classMem (syn_cop (syn_csn (syn_csn (.cv x))) A) B))) :=
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
  have dv_cache_0003 : t ∉ ((syn_cpw1 C)).fv :=
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
  have dv_cache_0006 : x ∉ ((Wff.classMem (syn_cop (syn_csn (.cv t)) A) B)).fv :=
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
  have dv_cache_0009 : t ∉ ((syn_csn (.cv x))).fv :=
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
    t ∉ ((Wff.classMem (syn_cop (syn_csn (syn_csn (.cv x))) A) B)).fv :=
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
  have p0000 := @g_elimapw1 t A B (syn_cpw1 C) dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    (Nominal.biimpRefl (syn_wrex t (syn_cpw1 C) (.classMem (syn_cop (syn_csn (.cv t)) A) B)))
  have p0002 := @g_elpw1 x (.cv t) C dv_cache_0004 dv_cache_0005
  have p0003 :=
    @g_anbi1i (.classMem (.cv t) (syn_cpw1 C))
      (syn_wrex x C (.classEq (.cv t) (syn_csn (.cv x))))
      (.classMem (syn_cop (syn_csn (.cv t)) A) B) p0002
  have p0004 :=
    @g_r19_41v (.classEq (.cv t) (syn_csn (.cv x)))
      (.classMem (syn_cop (syn_csn (.cv t)) A) B) x C dv_cache_0006
  have p0005 :=
    @g_bitr4i
      (syn_wa (.classMem (.cv t) (syn_cpw1 C)) (.classMem (syn_cop (syn_csn (.cv t)) A) B))
      (syn_wa (syn_wrex x C (.classEq (.cv t) (syn_csn (.cv x))))
        (.classMem (syn_cop (syn_csn (.cv t)) A) B))
      (syn_wrex x C (syn_wa (.classEq (.cv t) (syn_csn (.cv x)))
          (.classMem (syn_cop (syn_csn (.cv t)) A) B)))
      p0003 p0004
  have p0006 :=
    @g_exbii
      (syn_wa (.classMem (.cv t) (syn_cpw1 C)) (.classMem (syn_cop (syn_csn (.cv t)) A) B))
      (syn_wrex x C (syn_wa (.classEq (.cv t) (syn_csn (.cv x)))
          (.classMem (syn_cop (syn_csn (.cv t)) A) B)))
      t p0005
  have p0007 :=
    @g_rexcom4
      (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classMem (syn_cop (syn_csn (.cv t)) A) B))
      x t C dv_cache_0007 dv_cache_0008
  have p0008 := @g_snex (.cv x)
  have p0009 := @g_sneq (.cv t) (syn_csn (.cv x))
  have p0010 :=
    @g_opeq1d (.classEq (.cv t) (syn_csn (.cv x))) (syn_csn (.cv t))
      (syn_csn (syn_csn (.cv x))) A p0009
  have p0011 :=
    @g_eleq1d (.classEq (.cv t) (syn_csn (.cv x))) (syn_cop (syn_csn (.cv t)) A)
      (syn_cop (syn_csn (syn_csn (.cv x))) A) B p0010
  have p0012 :=
    @g_ceqsexv (.classMem (syn_cop (syn_csn (.cv t)) A) B)
      (.classMem (syn_cop (syn_csn (syn_csn (.cv x))) A) B) t (syn_csn (.cv x))
      dv_cache_0009 dv_cache_0010 p0008 p0011
  have p0013 :=
    @g_rexbii
      (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (.cv x)))
          (.classMem (syn_cop (syn_csn (.cv t)) A) B)))
      (.classMem (syn_cop (syn_csn (syn_csn (.cv x))) A) B) x C p0012
  have p0014 :=
    @g_bitr3i
      (syn_wex t (syn_wrex x C (syn_wa (.classEq (.cv t) (syn_csn (.cv x)))
            (.classMem (syn_cop (syn_csn (.cv t)) A) B))))
      (syn_wrex x C (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (.cv x)))
            (.classMem (syn_cop (syn_csn (.cv t)) A) B))))
      (syn_wrex x C (.classMem (syn_cop (syn_csn (syn_csn (.cv x))) A) B)) p0007 p0013
  have p0015 :=
    @g_bitri
      (syn_wex t (syn_wa (.classMem (.cv t) (syn_cpw1 C))
          (.classMem (syn_cop (syn_csn (.cv t)) A) B)))
      (syn_wex t (syn_wrex x C (syn_wa (.classEq (.cv t) (syn_csn (.cv x)))
            (.classMem (syn_cop (syn_csn (.cv t)) A) B))))
      (syn_wrex x C (.classMem (syn_cop (syn_csn (syn_csn (.cv x))) A) B)) p0006 p0014
  have p0016 :=
    @g_bitri (syn_wrex t (syn_cpw1 C) (.classMem (syn_cop (syn_csn (.cv t)) A) B))
      (syn_wex t (syn_wa (.classMem (.cv t) (syn_cpw1 C))
          (.classMem (syn_cop (syn_csn (.cv t)) A) B)))
      (syn_wrex x C (.classMem (syn_cop (syn_csn (syn_csn (.cv x))) A) B)) p0001 p0015
  have p0017 :=
    @g_bitri (.classMem A (syn_cima B (syn_cpw1 (syn_cpw1 C))))
      (syn_wrex t (syn_cpw1 C) (.classMem (syn_cop (syn_csn (.cv t)) A) B))
      (syn_wrex x C (.classMem (syn_cop (syn_csn (syn_csn (.cv x))) A) B)) p0000 p0016
  exact p0017

@[expose]
noncomputable def g_elima1c (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf
      (syn_wb (.classMem A (syn_cima B (syn_c1c)))
        (syn_wex x (.classMem (syn_cop (syn_csn (.cv x)) A) B))) :=
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
  have dv_cache_0003 : x ∉ ((syn_cvv)).fv :=
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
  have p0000 := @g_df1c2
  have p0001 := @g_imaeq2i (syn_c1c) (syn_cpw1 (syn_cvv)) B p0000
  have p0002 := @g_eleq2i (syn_cima B (syn_c1c)) (syn_cima B (syn_cpw1 (syn_cvv))) A p0001
  have p0003 := @g_elimapw1 x A B (syn_cvv) dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0004 := @g_rexv (.classMem (syn_cop (syn_csn (.cv x)) A) B) x
  have p0005 :=
    @g_n_3bitri (.classMem A (syn_cima B (syn_c1c)))
      (.classMem A (syn_cima B (syn_cpw1 (syn_cvv))))
      (syn_wrex x (syn_cvv) (.classMem (syn_cop (syn_csn (.cv x)) A) B))
      (syn_wex x (.classMem (syn_cop (syn_csn (.cv x)) A) B)) p0002 p0003 p0004
  exact p0005

@[expose]
noncomputable def g_elimapw11c (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf
      (syn_wb (.classMem A (syn_cima B (syn_cpw1 (syn_c1c))))
        (syn_wex x (.classMem (syn_cop (syn_csn (syn_csn (.cv x))) A) B))) :=
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
  have dv_cache_0003 : t ∉ ((syn_c1c)).fv :=
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
  have dv_cache_0005 : x ∉ ((Wff.classMem (syn_cop (syn_csn (.cv t)) A) B)).fv :=
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
  have dv_cache_0006 : t ∉ ((syn_csn (.cv x))).fv :=
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
    t ∉ ((Wff.classMem (syn_cop (syn_csn (syn_csn (.cv x))) A) B)).fv :=
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
  have p0000 := @g_elimapw1 t A B (syn_c1c) dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    (Nominal.biimpRefl (syn_wrex t (syn_c1c) (.classMem (syn_cop (syn_csn (.cv t)) A) B)))
  have p0002 := @g_el1c x (.cv t) dv_cache_0004
  have p0003 :=
    @g_anbi1i (.classMem (.cv t) (syn_c1c))
      (syn_wex x (.classEq (.cv t) (syn_csn (.cv x))))
      (.classMem (syn_cop (syn_csn (.cv t)) A) B) p0002
  have p0004 :=
    @g_n_19_41v (.classEq (.cv t) (syn_csn (.cv x)))
      (.classMem (syn_cop (syn_csn (.cv t)) A) B) x dv_cache_0005
  have p0005 :=
    @g_bitr4i
      (syn_wa (.classMem (.cv t) (syn_c1c)) (.classMem (syn_cop (syn_csn (.cv t)) A) B))
      (syn_wa (syn_wex x (.classEq (.cv t) (syn_csn (.cv x))))
        (.classMem (syn_cop (syn_csn (.cv t)) A) B))
      (syn_wex x (syn_wa (.classEq (.cv t) (syn_csn (.cv x)))
          (.classMem (syn_cop (syn_csn (.cv t)) A) B)))
      p0003 p0004
  have p0006 :=
    @g_exbii
      (syn_wa (.classMem (.cv t) (syn_c1c)) (.classMem (syn_cop (syn_csn (.cv t)) A) B))
      (syn_wex x (syn_wa (.classEq (.cv t) (syn_csn (.cv x)))
          (.classMem (syn_cop (syn_csn (.cv t)) A) B)))
      t p0005
  have p0007 :=
    @g_excom
      (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classMem (syn_cop (syn_csn (.cv t)) A) B))
      t x
  have p0008 :=
    @g_bitri
      (syn_wex t (syn_wa (.classMem (.cv t) (syn_c1c))
          (.classMem (syn_cop (syn_csn (.cv t)) A) B)))
      (syn_wex t (syn_wex x (syn_wa (.classEq (.cv t) (syn_csn (.cv x)))
            (.classMem (syn_cop (syn_csn (.cv t)) A) B))))
      (syn_wex x (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (.cv x)))
            (.classMem (syn_cop (syn_csn (.cv t)) A) B))))
      p0006 p0007
  have p0009 := @g_snex (.cv x)
  have p0010 := @g_sneq (.cv t) (syn_csn (.cv x))
  have p0011 :=
    @g_opeq1d (.classEq (.cv t) (syn_csn (.cv x))) (syn_csn (.cv t))
      (syn_csn (syn_csn (.cv x))) A p0010
  have p0012 :=
    @g_eleq1d (.classEq (.cv t) (syn_csn (.cv x))) (syn_cop (syn_csn (.cv t)) A)
      (syn_cop (syn_csn (syn_csn (.cv x))) A) B p0011
  have p0013 :=
    @g_ceqsexv (.classMem (syn_cop (syn_csn (.cv t)) A) B)
      (.classMem (syn_cop (syn_csn (syn_csn (.cv x))) A) B) t (syn_csn (.cv x))
      dv_cache_0006 dv_cache_0007 p0009 p0012
  have p0014 :=
    @g_exbii
      (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (.cv x)))
          (.classMem (syn_cop (syn_csn (.cv t)) A) B)))
      (.classMem (syn_cop (syn_csn (syn_csn (.cv x))) A) B) x p0013
  have p0015 :=
    @g_n_3bitri (syn_wrex t (syn_c1c) (.classMem (syn_cop (syn_csn (.cv t)) A) B))
      (syn_wex t (syn_wa (.classMem (.cv t) (syn_c1c))
          (.classMem (syn_cop (syn_csn (.cv t)) A) B)))
      (syn_wex x (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (.cv x)))
            (.classMem (syn_cop (syn_csn (.cv t)) A) B))))
      (syn_wex x (.classMem (syn_cop (syn_csn (syn_csn (.cv x))) A) B)) p0001 p0008 p0014
  have p0016 :=
    @g_bitri (.classMem A (syn_cima B (syn_cpw1 (syn_c1c))))
      (syn_wrex t (syn_c1c) (.classMem (syn_cop (syn_csn (.cv t)) A) B))
      (syn_wex x (.classMem (syn_cop (syn_csn (syn_csn (.cv x))) A) B)) p0000 p0015
  exact p0016

@[expose]
noncomputable def g_brres (A : Class) (B : Class) (C : Class) (D : Class) :
    Nominal.NPrf
      (syn_wb (syn_wbr A (syn_cres C D) B) (syn_wa (syn_wbr A C B) (.classMem A D))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cres C D))
  have p0001 := @g_breqi A B (syn_cres C D) (syn_cin C (syn_cxp D (syn_cvv))) p0000
  have p0002 := @g_brin A B C (syn_cxp D (syn_cvv))
  have p0003 := @g_anass (syn_wbr A C B) (.classMem A D) (.classMem B (syn_cvv))
  have p0004 := @g_brex A B C
  have p0005 :=
    @g_simprd (syn_wbr A C B) (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) p0004
  have p0006 := @g_adantr (syn_wbr A C B) (.classMem B (syn_cvv)) (.classMem A D) p0005
  have p0007 :=
    @g_pm4_71i (syn_wa (syn_wbr A C B) (.classMem A D)) (.classMem B (syn_cvv)) p0006
  have p0008 := @g_brxp A B D (syn_cvv)
  have p0009 :=
    @g_anbi2i (syn_wbr A (syn_cxp D (syn_cvv)) B)
      (syn_wa (.classMem A D) (.classMem B (syn_cvv))) (syn_wbr A C B) p0008
  have p0010 :=
    @g_n_3bitr4ri
      (syn_wa (syn_wa (syn_wbr A C B) (.classMem A D)) (.classMem B (syn_cvv)))
      (syn_wa (syn_wbr A C B) (syn_wa (.classMem A D) (.classMem B (syn_cvv))))
      (syn_wa (syn_wbr A C B) (.classMem A D))
      (syn_wa (syn_wbr A C B) (syn_wbr A (syn_cxp D (syn_cvv)) B)) p0003 p0007 p0009
  have p0011 :=
    @g_n_3bitri (syn_wbr A (syn_cres C D) B)
      (syn_wbr A (syn_cin C (syn_cxp D (syn_cvv))) B)
      (syn_wa (syn_wbr A C B) (syn_wbr A (syn_cxp D (syn_cvv)) B))
      (syn_wa (syn_wbr A C B) (.classMem A D)) p0001 p0002 p0010
  exact p0011

@[expose]
noncomputable def g_opelres (A : Class) (B : Class) (C : Class) (D : Class) :
    Nominal.NPrf
      (syn_wb (.classMem (syn_cop A B) (syn_cres C D))
        (syn_wa (.classMem (syn_cop A B) C) (.classMem A D))) :=
  by
  have p0000 := @g_brres A B C D
  have p0001 := (Nominal.biimpRefl (syn_wbr A (syn_cres C D) B))
  have p0002 := (Nominal.biimpRefl (syn_wbr A C B))
  have p0003 :=
    @g_anbi1i (syn_wbr A C B) (.classMem (syn_cop A B) C) (.classMem A D) p0002
  have p0004 :=
    @g_n_3bitr3i (syn_wbr A (syn_cres C D) B) (syn_wa (syn_wbr A C B) (.classMem A D))
      (.classMem (syn_cop A B) (syn_cres C D))
      (syn_wa (.classMem (syn_cop A B) C) (.classMem A D)) p0000 p0001 p0003
  exact p0004

@[expose]
noncomputable def g_dfima3 (A : Class) (B : Class) :
    Nominal.NPrf (.classEq (syn_cima A B) (syn_crn (syn_cres A B))) :=
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
  have dv_cache_0002 : y ∉ ((syn_cres A B)).fv :=
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
  have dv_cache_0005 : x ∉ ((syn_cima A B)).fv :=
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
  have dv_cache_0006 : x ∉ ((syn_crn (syn_cres A B))).fv :=
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
  have p0000 := @g_opelres (.cv y) (.cv x) A B
  have p0001 := @g_ancom (.classMem (syn_cop (.cv y) (.cv x)) A) (.classMem (.cv y) B)
  have p0002 :=
    @g_bitri (.classMem (syn_cop (.cv y) (.cv x)) (syn_cres A B))
      (syn_wa (.classMem (syn_cop (.cv y) (.cv x)) A) (.classMem (.cv y) B))
      (syn_wa (.classMem (.cv y) B) (.classMem (syn_cop (.cv y) (.cv x)) A)) p0000 p0001
  have p0003 :=
    @g_exbii (.classMem (syn_cop (.cv y) (.cv x)) (syn_cres A B))
      (syn_wa (.classMem (.cv y) B) (.classMem (syn_cop (.cv y) (.cv x)) A)) y p0002
  have p0004 := @g_elrn2 y (.cv x) (syn_cres A B) dv_cache_0001 dv_cache_0002
  have p0005 := @g_elima3 y (.cv x) A B dv_cache_0001 dv_cache_0003 dv_cache_0004
  have p0006 :=
    @g_n_3bitr4ri (syn_wex y (.classMem (syn_cop (.cv y) (.cv x)) (syn_cres A B)))
      (syn_wex y (syn_wa (.classMem (.cv y) B) (.classMem (syn_cop (.cv y) (.cv x)) A)))
      (.classMem (.cv x) (syn_crn (syn_cres A B))) (.classMem (.cv x) (syn_cima A B))
      p0003 p0004 p0005
  have p0007 :=
    @g_eqriv x (syn_cima A B) (syn_crn (syn_cres A B)) dv_cache_0005 dv_cache_0006 p0006
  exact p0007

@[expose]
noncomputable def g_dfima4 (x : Var) (y : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.classEq (syn_cima A B) (.cab y (syn_wex x
            (syn_wa (.classMem (.cv x) B) (.classMem (syn_cop (.cv x) (.cv y)) A))))) :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_ima y x A B
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0001 := (Nominal.biimpRefl (syn_wbr (.cv x) A (.cv y)))
  have p0002 :=
    @g_rexbii (syn_wbr (.cv x) A (.cv y)) (.classMem (syn_cop (.cv x) (.cv y)) A) x B
      p0001
  have p0003 := (Nominal.biimpRefl (syn_wrex x B (.classMem (syn_cop (.cv x) (.cv y)) A)))
  have p0004 :=
    @g_bitri (syn_wrex x B (syn_wbr (.cv x) A (.cv y)))
      (syn_wrex x B (.classMem (syn_cop (.cv x) (.cv y)) A))
      (syn_wex x (syn_wa (.classMem (.cv x) B) (.classMem (syn_cop (.cv x) (.cv y)) A)))
      p0002 p0003
  have p0005 :=
    @g_abbii (syn_wrex x B (syn_wbr (.cv x) A (.cv y)))
      (syn_wex x (syn_wa (.classMem (.cv x) B) (.classMem (syn_cop (.cv x) (.cv y)) A))) y
      p0004
  have p0006 :=
    @g_eqtri (syn_cima A B) (.cab y (syn_wrex x B (syn_wbr (.cv x) A (.cv y))))
      (.cab y (syn_wex x
          (syn_wa (.classMem (.cv x) B) (.classMem (syn_cop (.cv x) (.cv y)) A))))
      p0000 p0005
  exact p0006

@[expose]
noncomputable def g_rneq (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_crn A) (syn_crn B))) :=
  by
  have p0000 := @g_imaeq1 A B (syn_cvv)
  have p0001 := (Nominal.classEqRefl (syn_crn A))
  have p0002 := (Nominal.classEqRefl (syn_crn B))
  have p0003 :=
    @g_n_3eqtr4g (.classEq A B) (syn_cima A (syn_cvv)) (syn_cima B (syn_cvv)) (syn_crn A)
      (syn_crn B) p0000 p0001 p0002
  exact p0003

@[expose]
noncomputable def g_rneqi (A : Class) (B : Class)
    (hyp_rneqi_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (.classEq (syn_crn A) (syn_crn B)) :=
  by
  have p0000 := @g_rneq A B
  have p0001 := Nominal.mp hyp_rneqi_1 p0000
  exact p0001

@[expose]
noncomputable def g_rneqd (ph : Wff) (A : Class) (B : Class)
    (hyp_rneqd_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (syn_crn A) (syn_crn B))) :=
  by
  have p0000 := @g_rneq A B
  have p0001 :=
    @g_syl ph (.classEq A B) (.classEq (syn_crn A) (syn_crn B)) hyp_rneqd_1 p0000
  exact p0001

@[expose]
noncomputable def g_rnss (A : Class) (B : Class) :
    Nominal.NPrf (.imp (syn_wss A B) (syn_wss (syn_crn A) (syn_crn B))) :=
  by
  have p0000 := @g_cnvss A B
  have p0001 := @g_dmss (syn_ccnv A) (syn_ccnv B)
  have p0002 :=
    @g_syl (syn_wss A B) (syn_wss (syn_ccnv A) (syn_ccnv B))
      (syn_wss (syn_cdm (syn_ccnv A)) (syn_cdm (syn_ccnv B))) p0000 p0001
  have p0003 := @g_dfrn4 A
  have p0004 := @g_dfrn4 B
  have p0005 :=
    @g_n_3sstr4g (syn_wss A B) (syn_cdm (syn_ccnv A)) (syn_cdm (syn_ccnv B)) (syn_crn A)
      (syn_crn B) p0002 p0003 p0004
  exact p0005

@[expose]
noncomputable def g_brelrn (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (syn_wbr A C B) (.classMem B (syn_crn C))) :=
  by
  have p0000 := @g_breldm B A (syn_ccnv C)
  have p0001 := @g_brcnv B A C
  have p0002 := @g_bicomi (syn_wbr B (syn_ccnv C) A) (syn_wbr A C B) p0001
  have p0003 := @g_dfrn4 C
  have p0004 := @g_eleq2i (syn_crn C) (syn_cdm (syn_ccnv C)) B p0003
  have p0005 :=
    @g_n_3imtr4i (syn_wbr B (syn_ccnv C) A) (.classMem B (syn_cdm (syn_ccnv C)))
      (syn_wbr A C B) (.classMem B (syn_crn C)) p0000 p0002 p0004
  exact p0005

@[expose]
noncomputable def g_opelrn (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classMem (syn_cop A B) C) (.classMem B (syn_crn C))) :=
  by
  have p0000 := (Nominal.biimpRefl (syn_wbr A C B))
  have p0001 := @g_brelrn A B C
  have p0002 :=
    @g_sylbir (.classMem (syn_cop A B) C) (syn_wbr A C B) (.classMem B (syn_crn C)) p0000
      p0001
  exact p0002

@[expose]
noncomputable def g_dfrnf (x : Var) (y : Var) (A : Class) (dv_x_y : x ≠ y)
    (hyp_dfrnf_1 : Nominal.NPrf (syn_wnfc x A))
    (hyp_dfrnf_2 : Nominal.NPrf (syn_wnfc y A)) :
    Nominal.NPrf
      (.classEq (syn_crn A) (.cab y (syn_wex x (syn_wbr (.cv x) A (.cv y))))) :=
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
  have dv_cache_0006 : v ∉ ((syn_wbr (.cv x) A (.cv w))).fv :=
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
  have dv_cache_0009 : w ∉ ((syn_wex x (syn_wbr (.cv x) A (.cv y)))).fv :=
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
  have p0000 := @g_dfrn2 v w A dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 := @g_nfcv x (.cv v) dv_cache_0004
  have p0002 := @g_nfcv x (.cv w) dv_cache_0005
  have p0003 := @g_nfbr x (.cv v) (.cv w) A p0001 hyp_dfrnf_1 p0002
  have p0004 := @g_nfv (syn_wbr (.cv x) A (.cv w)) v dv_cache_0006
  have p0005 := @g_breq1 (.cv v) (.cv x) (.cv w) A
  have p0006_e02_recanon :
    Nominal.NPrf
      (.imp (.objEq v x) (syn_wb (syn_wbr (.cv v) A (.cv w)) (syn_wbr (.cv x) A (.cv w)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex
          syn_wex syn_cphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0005
  have p0006 :=
    @g_cbvex (syn_wbr (.cv v) A (.cv w)) (syn_wbr (.cv x) A (.cv w)) v x p0003 p0004
      p0006_e02_recanon
  have p0007 :=
    @g_abbii (syn_wex v (syn_wbr (.cv v) A (.cv w)))
      (syn_wex x (syn_wbr (.cv x) A (.cv w))) w p0006
  have p0008 := @g_nfcv y (.cv x) dv_cache_0007
  have p0009 := @g_nfcv y (.cv w) dv_cache_0008
  have p0010 := @g_nfbr y (.cv x) (.cv w) A p0008 hyp_dfrnf_2 p0009
  have p0011 := @g_nfex (syn_wbr (.cv x) A (.cv w)) y x p0010
  have p0012 := @g_nfv (syn_wex x (syn_wbr (.cv x) A (.cv y))) w dv_cache_0009
  have p0013 := @g_breq2 (.cv w) (.cv y) (.cv x) A
  have p0014 :=
    @g_exbidv (.classEq (.cv w) (.cv y)) (syn_wbr (.cv x) A (.cv w))
      (syn_wbr (.cv x) A (.cv y)) x dv_cache_0010 p0013
  have p0015_e02_recanon :
    Nominal.NPrf
      (.imp (.objEq w y) (syn_wb (syn_wex x (syn_wbr (.cv x) A (.cv w)))
          (syn_wex x (syn_wbr (.cv x) A (.cv y))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wex syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl
          syn_wrex syn_cphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0014
  have p0015 :=
    @g_cbvab (syn_wex x (syn_wbr (.cv x) A (.cv w)))
      (syn_wex x (syn_wbr (.cv x) A (.cv y))) w y p0011 p0012 p0015_e02_recanon
  have p0016 :=
    @g_n_3eqtri (syn_crn A) (.cab w (syn_wex v (syn_wbr (.cv v) A (.cv w))))
      (.cab w (syn_wex x (syn_wbr (.cv x) A (.cv w))))
      (.cab y (syn_wex x (syn_wbr (.cv x) A (.cv y)))) p0000 p0007 p0015
  exact p0016

@[expose]
noncomputable def g_rnopab (ph : Wff) (x : Var) (y : Var) (dv_x_y : x ≠ y) :
    Nominal.NPrf (.classEq (syn_crn (syn_copab x y ph)) (.cab y (syn_wex x ph))) :=
  by
  have dv_cache_0001 : x ≠ y := by exact (show x ≠ y from (by exact dv_x_y))
  have p0000 := @g_nfopab1 ph x y
  have p0001 := @g_nfopab2 ph x y
  have p0002 := @g_dfrnf x y (syn_copab x y ph) dv_cache_0001 p0000 p0001
  have p0003 := (Nominal.biimpRefl (syn_wbr (.cv x) (syn_copab x y ph) (.cv y)))
  have p0004 := @g_opabid ph x y
  have p0005 :=
    @g_bitri (syn_wbr (.cv x) (syn_copab x y ph) (.cv y))
      (.classMem (syn_cop (.cv x) (.cv y)) (syn_copab x y ph)) ph p0003 p0004
  have p0006 := @g_exbii (syn_wbr (.cv x) (syn_copab x y ph) (.cv y)) ph x p0005
  have p0007 :=
    @g_abbii (syn_wex x (syn_wbr (.cv x) (syn_copab x y ph) (.cv y))) (syn_wex x ph) y
      p0006
  have p0008 :=
    @g_eqtri (syn_crn (syn_copab x y ph))
      (.cab y (syn_wex x (syn_wbr (.cv x) (syn_copab x y ph) (.cv y))))
      (.cab y (syn_wex x ph)) p0002 p0007
  exact p0008

@[expose]
noncomputable def g_rnopab2 (x : Var) (y : Var) (A : Class) (B : Class) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.classEq (syn_crn (syn_copab x y (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B))))
        (.cab y (syn_wrex x A (.classEq (.cv y) B)))) :=
  by
  have dv_cache_0001 : x ≠ y := by exact (show x ≠ y from (by exact dv_x_y))
  have p0000 :=
    @g_rnopab (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B)) x y dv_cache_0001
  have p0001 := (Nominal.biimpRefl (syn_wrex x A (.classEq (.cv y) B)))
  have p0002 :=
    @g_abbii (syn_wrex x A (.classEq (.cv y) B))
      (syn_wex x (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B))) y p0001
  have p0003 :=
    @g_eqtr4i
      (syn_crn (syn_copab x y (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B))))
      (.cab y (syn_wex x (syn_wa (.classMem (.cv x) A) (.classEq (.cv y) B))))
      (.cab y (syn_wrex x A (.classEq (.cv y) B))) p0000 p0002
  exact p0003

@[expose]
noncomputable def g_rn0 : Nominal.NPrf (.classEq (syn_crn (syn_c0)) (syn_c0)) :=
  by
  have p0000 := @g_dm0
  have p0001 := @g_dm0rn0 (syn_c0)
  have p0002 :=
    @g_mpbi (.classEq (syn_cdm (syn_c0)) (syn_c0)) (.classEq (syn_crn (syn_c0)) (syn_c0))
      p0000 p0001
  exact p0002


end NFChoice.DirectNominalPrf.WPPReplay

end

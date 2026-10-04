/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk010Compact001Block019

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk010Compact001Part065`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_brswap2`. -/
@[expose]
noncomputable def gBrswap2 (A : Class) (B : Class) (C : Class)
    (hyp_br1st_1 : Nominal.NPrf (.classMem B (synCvv)))
    (hyp_brswap_2 : Nominal.NPrf (.classMem C (synCvv))) :
    Nominal.NPrf
      (synWb (synWbr A (synCswap) (synCop B C)) (.classEq A (synCop C B))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  let x : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  let w : Var := freshVar proofSupport 2
  let y : Var := freshVar proofSupport 3
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
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_C : z ∉ C.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_w_not_B : w ∉ B.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_w_not_C : w ∉ C.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_z_ne_x : z ≠ x := Ne.symm fresh_x_ne_z
  have fresh_x_ne_w : x ≠ w :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_w_ne_x : w ≠ x := Ne.symm fresh_x_ne_w
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_z_ne_w : z ≠ w :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_w_ne_z : w ≠ z := Ne.symm fresh_z_ne_w
  have fresh_z_ne_y : z ≠ y :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_y_ne_z : y ≠ z := Ne.symm fresh_z_ne_y
  have fresh_w_ne_y : w ≠ y :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have dv_cache_0001 : z ∉ ((Wff.classEq (.cv x) A)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_x, fresh_z_not_A, or_false, not_false_eq_true])
  have dv_cache_0002 : w ∉ ((Wff.classEq (.cv x) A)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_x, fresh_w_not_A, or_false, not_false_eq_true])
  have dv_cache_0003 : z ∉ ((Wff.classEq (.cv y) (synCop B C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_y, fresh_z_not_B, fresh_z_not_C, or_false,
          not_false_eq_true])
  have dv_cache_0004 : w ∉ ((Wff.classEq (.cv y) (synCop B C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_y, fresh_w_not_B, fresh_w_not_C, or_false,
          not_false_eq_true])
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
  have dv_cache_0006 : z ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_B, not_false_eq_true])
  have dv_cache_0007 : w ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_C, not_false_eq_true])
  have dv_cache_0008 : z ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_C, not_false_eq_true])
  have dv_cache_0009 : z ∉ ((Wff.classEq A (synCop C B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          fresh_z_not_A, fresh_z_not_C, fresh_z_not_B, or_false, not_false_eq_true])
  have dv_cache_0010 : w ∉ ((Wff.classEq A (synCop (.cv z) B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_w_not_A, fresh_w_ne_z, fresh_w_not_B, or_false,
          not_false_eq_true])
  have dv_cache_0011 : w ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show w ≠ z from (by exact fresh_w_ne_z))
  have dv_cache_0012 : w ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show w ≠ x from (by exact fresh_w_ne_x))
  have dv_cache_0013 : w ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact (show w ≠ y from (by exact fresh_w_ne_y))
  have dv_cache_0014 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0015 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0016 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0017 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0018 : y ∉ (A).fv :=
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
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0019 : x ∉ ((synCop B C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          fresh_x_not_B, fresh_x_not_C, or_false, not_false_eq_true])
  have dv_cache_0020 : y ∉ ((synCop B C)).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          fresh_y_not_B, fresh_y_not_C, or_false, not_false_eq_true])
  have dv_cache_0021 : x ∉ ((Wff.classEq A (synCop C B))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_C, fresh_x_not_B, or_false, not_false_eq_true])
  have dv_cache_0022 : y ∉ ((Wff.classEq A (synCop C B))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          fresh_y_not_A, fresh_y_not_C, fresh_y_not_B, or_false, not_false_eq_true])
  have p0000 := @gBrex A (synCop B C) (synCswap)
  have p0001 :=
    @gSimpld (synWbr A (synCswap) (synCop B C)) (.classMem A (synCvv))
      (.classMem (synCop B C) (synCvv)) p0000
  have p0002 := @gOpex C B hyp_brswap_2 hyp_br1st_1
  have p0003 := @gEleq1 A (synCop C B) (synCvv)
  have p0004 :=
    @gMpbiri (.classEq A (synCop C B)) (.classMem A (synCvv))
      (.classMem (synCop C B) (synCvv)) p0002 p0003
  have p0005 := @gOpex B C hyp_br1st_1 hyp_brswap_2
  have p0006 := @gEqeq1 (.cv x) A (synCop (.cv z) (.cv w))
  have p0007 :=
    @gAnbi1d (.classEq (.cv x) A) (.classEq (.cv x) (synCop (.cv z) (.cv w)))
      (.classEq A (synCop (.cv z) (.cv w))) (.classEq (.cv y) (synCop (.cv w) (.cv z)))
      p0006
  have p0008 :=
    @gN2exbidv (.classEq (.cv x) A)
      (synWa (.classEq (.cv x) (synCop (.cv z) (.cv w)))
        (.classEq (.cv y) (synCop (.cv w) (.cv z))))
      (synWa (.classEq A (synCop (.cv z) (.cv w)))
        (.classEq (.cv y) (synCop (.cv w) (.cv z))))
      z w dv_cache_0001 dv_cache_0002 p0007
  have p0009 := @gEqeq1 (.cv y) (synCop B C) (synCop (.cv w) (.cv z))
  have p0010 :=
    @gAnbi2d (.classEq (.cv y) (synCop B C))
      (.classEq (.cv y) (synCop (.cv w) (.cv z)))
      (.classEq (synCop B C) (synCop (.cv w) (.cv z)))
      (.classEq A (synCop (.cv z) (.cv w))) p0009
  have p0011 := @gEqcom (synCop B C) (synCop (.cv w) (.cv z))
  have p0012 := @gOpth (.cv w) (.cv z) B C
  have p0013 :=
    @gBitri (.classEq (synCop B C) (synCop (.cv w) (.cv z)))
      (.classEq (synCop (.cv w) (.cv z)) (synCop B C))
      (synWa (.classEq (.cv w) B) (.classEq (.cv z) C)) p0011 p0012
  have p0014 :=
    @gAnbi1i (.classEq (synCop B C) (synCop (.cv w) (.cv z)))
      (synWa (.classEq (.cv w) B) (.classEq (.cv z) C))
      (.classEq A (synCop (.cv z) (.cv w))) p0013
  have p0015 :=
    @gAncom (.classEq A (synCop (.cv z) (.cv w)))
      (.classEq (synCop B C) (synCop (.cv w) (.cv z)))
  have p0016 :=
    (Nominal.biimpRefl (synW3a (.classEq (.cv w) B) (.classEq (.cv z) C)
        (.classEq A (synCop (.cv z) (.cv w)))))
  have p0017 :=
    @gN3bitr4ri
      (synWa (.classEq (synCop B C) (synCop (.cv w) (.cv z)))
        (.classEq A (synCop (.cv z) (.cv w))))
      (synWa (synWa (.classEq (.cv w) B) (.classEq (.cv z) C))
        (.classEq A (synCop (.cv z) (.cv w))))
      (synWa (.classEq A (synCop (.cv z) (.cv w)))
        (.classEq (synCop B C) (synCop (.cv w) (.cv z))))
      (synW3a (.classEq (.cv w) B) (.classEq (.cv z) C) (.classEq A (synCop (.cv z) (.cv w))))
      p0014 p0015 p0016
  have p0018 :=
    @gSyl6bbr (.classEq (.cv y) (synCop B C))
      (synWa (.classEq A (synCop (.cv z) (.cv w)))
        (.classEq (.cv y) (synCop (.cv w) (.cv z))))
      (synWa (.classEq A (synCop (.cv z) (.cv w)))
        (.classEq (synCop B C) (synCop (.cv w) (.cv z))))
      (synW3a (.classEq (.cv w) B) (.classEq (.cv z) C) (.classEq A (synCop (.cv z) (.cv w))))
      p0010 p0017
  have p0019 :=
    @gN2exbidv (.classEq (.cv y) (synCop B C))
      (synWa (.classEq A (synCop (.cv z) (.cv w)))
        (.classEq (.cv y) (synCop (.cv w) (.cv z))))
      (synW3a (.classEq (.cv w) B) (.classEq (.cv z) C) (.classEq A (synCop (.cv z) (.cv w))))
      z w dv_cache_0003 dv_cache_0004 p0018
  have p0020 :=
    @gExcom
      (synW3a (.classEq (.cv w) B) (.classEq (.cv z) C) (.classEq A (synCop (.cv z) (.cv w))))
      z w
  have p0021 :=
    @gSyl6bb (.classEq (.cv y) (synCop B C))
      (synWex z (synWex w (synWa (.classEq A (synCop (.cv z) (.cv w)))
            (.classEq (.cv y) (synCop (.cv w) (.cv z))))))
      (synWex z (synWex w (synW3a (.classEq (.cv w) B) (.classEq (.cv z) C)
            (.classEq A (synCop (.cv z) (.cv w))))))
      (synWex w (synWex z (synW3a (.classEq (.cv w) B) (.classEq (.cv z) C)
            (.classEq A (synCop (.cv z) (.cv w))))))
      p0019 p0020
  have p0022 := @gOpeq2 (.cv w) B (.cv z)
  have p0023 :=
    @gEqeq2d (.classEq (.cv w) B) (synCop (.cv z) (.cv w)) (synCop (.cv z) B) A p0022
  have p0024 := @gOpeq1 (.cv z) C B
  have p0025 := @gEqeq2d (.classEq (.cv z) C) (synCop (.cv z) B) (synCop C B) A p0024
  have p0026 :=
    @gCeqsex2v (.classEq A (synCop (.cv z) (.cv w))) (.classEq A (synCop (.cv z) B))
      (.classEq A (synCop C B)) w z B C dv_cache_0005 dv_cache_0006 dv_cache_0007
      dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 hyp_br1st_1 hyp_brswap_2
      p0023 p0025
  have p0027 :=
    @gSyl6bb (.classEq (.cv y) (synCop B C))
      (synWex z (synWex w (synWa (.classEq A (synCop (.cv z) (.cv w)))
            (.classEq (.cv y) (synCop (.cv w) (.cv z))))))
      (synWex w (synWex z (synW3a (.classEq (.cv w) B) (.classEq (.cv z) C)
            (.classEq A (synCop (.cv z) (.cv w))))))
      (.classEq A (synCop C B)) p0021 p0026
  have p0028 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfSwap x y z w
      dv_cache_0012 dv_cache_0013 dv_cache_0011 dv_cache_0014 dv_cache_0015 dv_cache_0016
  have p0029 :=
    @gBrabg
      (synWex z (synWex w (synWa (.classEq (.cv x) (synCop (.cv z) (.cv w)))
            (.classEq (.cv y) (synCop (.cv w) (.cv z))))))
      (synWex z (synWex w (synWa (.classEq A (synCop (.cv z) (.cv w)))
            (.classEq (.cv y) (synCop (.cv w) (.cv z))))))
      (.classEq A (synCop C B)) x y A (synCop B C) (synCvv) (synCvv) (synCswap)
      dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
      dv_cache_0014 p0008 p0027 p0028
  have p0030 :=
    @gMpan2 (.classMem A (synCvv)) (.classMem (synCop B C) (synCvv))
      (synWb (synWbr A (synCswap) (synCop B C)) (.classEq A (synCop C B))) p0005
      p0029
  have p0031 :=
    @gPm521nii (synWbr A (synCswap) (synCop B C)) (.classMem A (synCvv))
      (.classEq A (synCop C B)) p0001 p0004 p0030
  exact p0031

/-- Checked nominal proof certificate identified upstream as `g_opabid2`. -/
@[expose]
noncomputable def gOpabid2 (x : Var) (y : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf (.classEq (synCopab x y (.classMem (synCop (.cv x) (.cv y)) A)) A) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv
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
  have fresh_z_ne_w : z ≠ w :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : x ∉ ((Class.cv z)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_z, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_z, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((Class.cv w)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_w, not_false_eq_true])
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
  have dv_cache_0005 : x ∉ ((Wff.classMem (synCop (.cv z) (.cv w)) A)).fv :=
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
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_z, fresh_x_ne_w, dv_A_x, or_false,
          not_false_eq_true])
  have dv_cache_0006 : y ∉ ((Wff.classMem (synCop (.cv z) (.cv w)) A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_z, fresh_y_ne_w, dv_A_y, or_false,
          not_false_eq_true])
  have dv_cache_0007 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0008 : z ∉ ((synCopab x y (.classMem (synCop (.cv x) (.cv y)) A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copab,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_y, fresh_z_not_A, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0009 : w ∉ ((synCopab x y (.classMem (synCop (.cv x) (.cv y)) A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copab,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_w_ne_x, fresh_w_ne_y, fresh_w_not_A, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0010 : z ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_A, not_false_eq_true])
  have dv_cache_0011 : w ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_A, not_false_eq_true])
  have dv_cache_0012 : z ≠ w :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show z ≠ w from (by exact fresh_z_ne_w))
  have p0000 := @gVex z
  have p0001 := @gVex w
  have p0002 := @gOpeq1 (.cv x) (.cv z) (.cv y)
  have p0003_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq x z) (.classEq (synCop (.cv x) (.cv y)) (synCop (.cv z) (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCop synCun synCnin synWnan synWa synCcompl synWrex synWex
          synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0002
  have p0003 :=
    @gEleq1d (.objEq x z) (synCop (.cv x) (.cv y)) (synCop (.cv z) (.cv y)) A
      p0003_e00_recanon
  have p0004 := @gOpeq2 (.cv y) (.cv w) (.cv z)
  have p0005_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq y w) (.classEq (synCop (.cv z) (.cv y)) (synCop (.cv z) (.cv w)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCop synCun synCnin synWnan synWa synCcompl synWrex synWex
          synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0004
  have p0005 :=
    @gEleq1d (.objEq y w) (synCop (.cv z) (.cv y)) (synCop (.cv z) (.cv w)) A
      p0005_e00_recanon
  have p0006_e02_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv x) (.cv z)) (synWb (.classMem (synCop (.cv x) (.cv y)) A)
          (.classMem (synCop (.cv z) (.cv y)) A))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCop synCun synCnin synWnan synWa synCcompl synWrex synWex
          synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0003
  have p0006_e03_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv y) (.cv w)) (synWb (.classMem (synCop (.cv z) (.cv y)) A)
          (.classMem (synCop (.cv z) (.cv w)) A))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCop synCun synCnin synWnan synWa synCcompl synWrex synWex
          synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0005
  have p0006 :=
    @gOpelopab (.classMem (synCop (.cv x) (.cv y)) A)
      (.classMem (synCop (.cv z) (.cv y)) A) (.classMem (synCop (.cv z) (.cv w)) A) x y
      (.cv z) (.cv w) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007 p0000 p0001 p0006_e02_recanon
      p0006_e03_recanon
  have p0007 :=
    @gEqrelriv z w (synCopab x y (.classMem (synCop (.cv x) (.cv y)) A)) A
      dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_inopab`. -/
@[expose]
noncomputable def gInopab (ph : Wff) (ps : Wff) (x : Var) (y : Var) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.classEq (synCin (synCopab x y ph) (synCopab x y ps))
        (synCopab x y (synWa ph ps))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
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
  have fresh_z_not_ps : z ∉ ps.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_w_not_ph : w ∉ ph.fv := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_w_not_ps : w ∉ ps.fv := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_w : x ≠ w := Ne.symm fresh_w_ne_x
  have fresh_z_ne_w : z ≠ w :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : x ∉ ((Class.cv w)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_w, not_false_eq_true])
  have dv_cache_0002 : x ≠ y := by
    clear dv_cache_0001
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0003 : z ∉ ((synCin (synCopab x y ph) (synCopab x y ps))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copab, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_z_not_ph, fresh_z_ne_x,
          fresh_z_not_ps, or_false, and_false, not_false_eq_true])
  have dv_cache_0004 : w ∉ ((synCin (synCopab x y ph) (synCopab x y ps))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copab, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_w_not_ph, fresh_w_ne_x,
          fresh_w_not_ps, or_false, and_false, not_false_eq_true])
  have dv_cache_0005 : z ∉ ((synCopab x y (synWa ph ps))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_z_not_ph, fresh_z_not_ps,
          fresh_z_ne_x, or_false, and_false, not_false_eq_true])
  have dv_cache_0006 : w ∉ ((synCopab x y (synWa ph ps))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_w_not_ph, fresh_w_not_ps,
          fresh_w_ne_x, or_false, and_false, not_false_eq_true])
  have dv_cache_0007 : z ≠ w :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show z ≠ w from (by exact fresh_z_ne_w))
  have p0000 := @gSbcan (synWsbc (.cv w) y ph) (synWsbc (.cv w) y ps) x (.cv z)
  have p0001 := @gSbcan ph ps y (.cv w)
  have p0002 :=
    @gSbcbii (synWsbc (.cv w) y (synWa ph ps))
      (synWa (synWsbc (.cv w) y ph) (synWsbc (.cv w) y ps)) x (.cv z) p0001
  have p0003 := @gOpelopabsb ph x y (.cv z) (.cv w) dv_cache_0001 dv_cache_0002
  have p0004 := @gOpelopabsb ps x y (.cv z) (.cv w) dv_cache_0001 dv_cache_0002
  have p0005 :=
    @gAnbi12i (.classMem (synCop (.cv z) (.cv w)) (synCopab x y ph))
      (synWsbc (.cv z) x (synWsbc (.cv w) y ph))
      (.classMem (synCop (.cv z) (.cv w)) (synCopab x y ps))
      (synWsbc (.cv z) x (synWsbc (.cv w) y ps)) p0003 p0004
  have p0006 :=
    @gN3bitr4ri
      (synWsbc (.cv z) x (synWa (synWsbc (.cv w) y ph) (synWsbc (.cv w) y ps)))
      (synWa (synWsbc (.cv z) x (synWsbc (.cv w) y ph))
        (synWsbc (.cv z) x (synWsbc (.cv w) y ps)))
      (synWsbc (.cv z) x (synWsbc (.cv w) y (synWa ph ps)))
      (synWa (.classMem (synCop (.cv z) (.cv w)) (synCopab x y ph))
        (.classMem (synCop (.cv z) (.cv w)) (synCopab x y ps)))
      p0000 p0002 p0005
  have p0007 := @gElin (synCop (.cv z) (.cv w)) (synCopab x y ph) (synCopab x y ps)
  have p0008 :=
    @gOpelopabsb (synWa ph ps) x y (.cv z) (.cv w) dv_cache_0001 dv_cache_0002
  have p0009 :=
    @gN3bitr4i
      (synWa (.classMem (synCop (.cv z) (.cv w)) (synCopab x y ph))
        (.classMem (synCop (.cv z) (.cv w)) (synCopab x y ps)))
      (synWsbc (.cv z) x (synWsbc (.cv w) y (synWa ph ps)))
      (.classMem (synCop (.cv z) (.cv w)) (synCin (synCopab x y ph) (synCopab x y ps)))
      (.classMem (synCop (.cv z) (.cv w)) (synCopab x y (synWa ph ps))) p0006 p0007
      p0008
  have p0010 :=
    @gEqrelriv z w (synCin (synCopab x y ph) (synCopab x y ps))
      (synCopab x y (synWa ph ps)) dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 p0009
  exact p0010

/-- Checked nominal proof certificate identified upstream as `g_inxp`. -/
@[expose]
noncomputable def gInxp (A : Class) (B : Class) (C : Class) (D : Class) :
    Nominal.NPrf
      (.classEq (synCin (synCxp A B) (synCxp C D)) (synCxp (synCin A C) (synCin B D))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ D.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
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
  have fresh_x_not_D : x ∉ D.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
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
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : x ≠ y := by exact (show x ≠ y from (by exact fresh_x_ne_y))
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
  have dv_cache_0005 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_B, not_false_eq_true])
  have dv_cache_0006 : x ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_C, not_false_eq_true])
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
        simp only [fresh_x_not_D, not_false_eq_true])
  have dv_cache_0009 : y ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_D, not_false_eq_true])
  have dv_cache_0010 : x ∉ ((synCin A C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_C, or_false, not_false_eq_true])
  have dv_cache_0011 : y ∉ ((synCin A C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, Finset.mem_union,
          fresh_y_not_A, fresh_y_not_C, or_false, not_false_eq_true])
  have dv_cache_0012 : x ∉ ((synCin B D)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, Finset.mem_union,
          fresh_x_not_B, fresh_x_not_D, or_false, not_false_eq_true])
  have dv_cache_0013 : y ∉ ((synCin B D)).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, Finset.mem_union,
          fresh_y_not_B, fresh_y_not_D, or_false, not_false_eq_true])
  have p0000 :=
    @gInopab (synWa (.classMem (.cv x) A) (.classMem (.cv y) B))
      (synWa (.classMem (.cv x) C) (.classMem (.cv y) D)) x y dv_cache_0001
  have p0001 :=
    @gAn4 (.classMem (.cv x) A) (.classMem (.cv y) B) (.classMem (.cv x) C)
      (.classMem (.cv y) D)
  have p0002 := @gElin (.cv x) A C
  have p0003 := @gElin (.cv y) B D
  have p0004 :=
    @gAnbi12i (.classMem (.cv x) (synCin A C))
      (synWa (.classMem (.cv x) A) (.classMem (.cv x) C))
      (.classMem (.cv y) (synCin B D))
      (synWa (.classMem (.cv y) B) (.classMem (.cv y) D)) p0002 p0003
  have p0005 :=
    @gBitr4i
      (synWa (synWa (.classMem (.cv x) A) (.classMem (.cv y) B))
        (synWa (.classMem (.cv x) C) (.classMem (.cv y) D)))
      (synWa (synWa (.classMem (.cv x) A) (.classMem (.cv x) C))
        (synWa (.classMem (.cv y) B) (.classMem (.cv y) D)))
      (synWa (.classMem (.cv x) (synCin A C)) (.classMem (.cv y) (synCin B D))) p0001
      p0004
  have p0006 :=
    @gOpabbii
      (synWa (synWa (.classMem (.cv x) A) (.classMem (.cv y) B))
        (synWa (.classMem (.cv x) C) (.classMem (.cv y) D)))
      (synWa (.classMem (.cv x) (synCin A C)) (.classMem (.cv y) (synCin B D))) x y
      p0005
  have p0007 :=
    @gEqtri
      (synCin (synCopab x y (synWa (.classMem (.cv x) A) (.classMem (.cv y) B)))
        (synCopab x y (synWa (.classMem (.cv x) C) (.classMem (.cv y) D))))
      (synCopab x y (synWa (synWa (.classMem (.cv x) A) (.classMem (.cv y) B))
          (synWa (.classMem (.cv x) C) (.classMem (.cv y) D))))
      (synCopab x y
        (synWa (.classMem (.cv x) (synCin A C)) (.classMem (.cv y) (synCin B D))))
      p0000 p0006
  have p0008 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfXp x y A B
      dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0001
  have p0009 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfXp x y C D
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0001
  have p0010 :=
    @gIneq12i (synCxp A B)
      (synCopab x y (synWa (.classMem (.cv x) A) (.classMem (.cv y) B))) (synCxp C D)
      (synCopab x y (synWa (.classMem (.cv x) C) (.classMem (.cv y) D))) p0008 p0009
  have p0011 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfXp x y (synCin A C)
      (synCin B D) dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0001
  have p0012 :=
    @gN3eqtr4i
      (synCin (synCopab x y (synWa (.classMem (.cv x) A) (.classMem (.cv y) B)))
        (synCopab x y (synWa (.classMem (.cv x) C) (.classMem (.cv y) D))))
      (synCopab x y
        (synWa (.classMem (.cv x) (synCin A C)) (.classMem (.cv y) (synCin B D))))
      (synCin (synCxp A B) (synCxp C D)) (synCxp (synCin A C) (synCin B D)) p0007
      p0010 p0011
  exact p0012

/-- Checked nominal proof certificate identified upstream as `g_opabbi2i`. -/
@[expose]
noncomputable def gOpabbi2i (ph : Wff) (x : Var) (y : Var) (A : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_x_y : x ≠ y)
    (hyp_opabbi2i_1 : Nominal.NPrf (synWb (.classMem (synCop (.cv x) (.cv y)) A) ph)) :
    Nominal.NPrf (.classEq A (synCopab x y ph)) :=
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
  have p0000 := @gOpabid2 x y A dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 := @gOpabbii (.classMem (synCop (.cv x) (.cv y)) A) ph x y hyp_opabbi2i_1
  have p0002 :=
    @gEqtr3i (synCopab x y (.classMem (synCop (.cv x) (.cv y)) A)) A (synCopab x y ph)
      p0000 p0001
  exact p0002


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk010Compact001Part066`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_ideqg`. -/
@[expose]
noncomputable def gIdeqg (A : Class) (B : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem B V) (synWb (synWbr A (synCid) B) (.classEq A B))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ V.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
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
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : x ≠ y := by exact (show x ≠ y from (by exact fresh_x_ne_y))
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
  have dv_cache_0005 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_B, not_false_eq_true])
  have dv_cache_0006 : x ∉ ((Wff.classEq A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true])
  have dv_cache_0007 : y ∉ ((Wff.classEq A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
          fresh_y_not_A, fresh_y_not_B, or_false, not_false_eq_true])
  have p0000 := @gBrex A B (synCid)
  have p0001 :=
    @gAdantl (synWbr A (synCid) B)
      (synWa (.classMem A (synCvv)) (.classMem B (synCvv))) (.classMem B V) p0000
  have p0002 := @gSimpr (.classMem B V) (.classEq A B)
  have p0003 := @gElex B V
  have p0004 := @gAdantr (.classMem B V) (.classMem B (synCvv)) (.classEq A B) p0003
  have p0005 :=
    @gEqeltrd (synWa (.classMem B V) (.classEq A B)) A B (synCvv) p0002 p0004
  have p0006 :=
    @gJca (synWa (.classMem B V) (.classEq A B)) (.classMem A (synCvv))
      (.classMem B (synCvv)) p0005 p0004
  have p0007 := @gEqeq1 (.cv x) A (.cv y)
  have p0008 := @gEqeq2 (.cv y) B A
  have p0009 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfId x y dv_cache_0001
  have p0010_e00_recanon :
    Nominal.NPrf (.imp (.classEq (.cv x) A) (synWb (.objEq x y) (.classEq A (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0007
  have p0010 :=
    @gBrabg (.objEq x y) (.classEq A (.cv y)) (.classEq A B) x y A B (synCvv) (synCvv)
      (synCid) dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0001 p0010_e00_recanon p0008 p0009
  have p0011 :=
    @gPm521nd (.classMem B V) (synWbr A (synCid) B) (.classEq A B)
      (synWa (.classMem A (synCvv)) (.classMem B (synCvv))) p0001 p0006 p0010
  exact p0011

/-- Checked nominal proof certificate identified upstream as `g_ideq`. -/
@[expose]
noncomputable def gIdeq (A : Class) (B : Class)
    (hyp_ideq_1 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf (synWb (synWbr A (synCid) B) (.classEq A B)) :=
  by
  have p0000 := @gIdeqg A B (synCvv)
  have p0001 := Nominal.mp hyp_ideq_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_ididg`. -/
@[expose]
noncomputable def gIdidg (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (synWbr A (synCid) A)) :=
  by
  have p0000 := @gEqid A
  have p0001 := @gIdeqg A A V
  have p0002 :=
    @gMpbiri (.classMem A V) (synWbr A (synCid) A) (.classEq A A) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_coss1`. -/
@[expose]
noncomputable def gCoss1 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (synWss A B) (synWss (synCcom A C) (synCcom B C))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
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
  have fresh_x_not_C : x ∉ C.fv := by
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
  have fresh_y_not_C : y ∉ C.fv := by
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
  have fresh_z_not_C : z ∉ C.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y := Ne.symm fresh_y_ne_z
  have dv_cache_0001 : y ∉ ((synWss A B)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union,
          fresh_y_not_A, fresh_y_not_B, or_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((synWss A B)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true])
  have dv_cache_0003 : z ∉ ((synWss A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union,
          fresh_z_not_A, fresh_z_not_B, or_false, not_false_eq_true])
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
  have dv_cache_0006 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0007 : x ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_C, not_false_eq_true])
  have dv_cache_0008 : z ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_C, not_false_eq_true])
  have dv_cache_0009 : y ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_C, not_false_eq_true])
  have dv_cache_0010 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0011 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0012 : z ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show z ≠ y from (by exact fresh_z_ne_y))
  have dv_cache_0013 : x ∉ (B).fv :=
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
        simp only [fresh_x_not_B, not_false_eq_true])
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
  have p0000 := @gId (synWss A B)
  have p0001 := @gSsbrd (synWss A B) A B (.cv y) (.cv z) p0000
  have p0002 :=
    @gAnim2d (synWss A B) (synWbr (.cv y) A (.cv z)) (synWbr (.cv y) B (.cv z))
      (synWbr (.cv x) C (.cv y)) p0001
  have p0003 :=
    @gEximdv (synWss A B)
      (synWa (synWbr (.cv x) C (.cv y)) (synWbr (.cv y) A (.cv z)))
      (synWa (synWbr (.cv x) C (.cv y)) (synWbr (.cv y) B (.cv z))) y dv_cache_0001
      p0002
  have p0004 :=
    @gSsopab2dv (synWss A B)
      (synWex y (synWa (synWbr (.cv x) C (.cv y)) (synWbr (.cv y) A (.cv z))))
      (synWex y (synWa (synWbr (.cv x) C (.cv y)) (synWbr (.cv y) B (.cv z)))) x z
      dv_cache_0002 dv_cache_0003 p0003
  have p0005 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfCo x z y A C
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
      dv_cache_0010 dv_cache_0011 dv_cache_0012
  have p0006 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfCo x z y B C
      dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0007 dv_cache_0008 dv_cache_0009
      dv_cache_0010 dv_cache_0011 dv_cache_0012
  have p0007 :=
    @gN3sstr4g (synWss A B)
      (synCopab x z
        (synWex y (synWa (synWbr (.cv x) C (.cv y)) (synWbr (.cv y) A (.cv z)))))
      (synCopab x z
        (synWex y (synWa (synWbr (.cv x) C (.cv y)) (synWbr (.cv y) B (.cv z)))))
      (synCcom A C) (synCcom B C) p0004 p0005 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_coss2`. -/
@[expose]
noncomputable def gCoss2 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (synWss A B) (synWss (synCcom C A) (synCcom C B))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
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
  have fresh_x_not_C : x ∉ C.fv := by
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
  have fresh_y_not_C : y ∉ C.fv := by
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
  have fresh_z_not_C : z ∉ C.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y := Ne.symm fresh_y_ne_z
  have dv_cache_0001 : y ∉ ((synWss A B)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union,
          fresh_y_not_A, fresh_y_not_B, or_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((synWss A B)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true])
  have dv_cache_0003 : z ∉ ((synWss A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union,
          fresh_z_not_A, fresh_z_not_B, or_false, not_false_eq_true])
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
        simp only [fresh_x_not_A, not_false_eq_true])
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
  have dv_cache_0010 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0011 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0012 : z ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show z ≠ y from (by exact fresh_z_ne_y))
  have dv_cache_0013 : x ∉ (B).fv :=
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
        simp only [fresh_x_not_B, not_false_eq_true])
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
  have p0000 := @gId (synWss A B)
  have p0001 := @gSsbrd (synWss A B) A B (.cv x) (.cv y) p0000
  have p0002 :=
    @gAnim1d (synWss A B) (synWbr (.cv x) A (.cv y)) (synWbr (.cv x) B (.cv y))
      (synWbr (.cv y) C (.cv z)) p0001
  have p0003 :=
    @gEximdv (synWss A B)
      (synWa (synWbr (.cv x) A (.cv y)) (synWbr (.cv y) C (.cv z)))
      (synWa (synWbr (.cv x) B (.cv y)) (synWbr (.cv y) C (.cv z))) y dv_cache_0001
      p0002
  have p0004 :=
    @gSsopab2dv (synWss A B)
      (synWex y (synWa (synWbr (.cv x) A (.cv y)) (synWbr (.cv y) C (.cv z))))
      (synWex y (synWa (synWbr (.cv x) B (.cv y)) (synWbr (.cv y) C (.cv z)))) x z
      dv_cache_0002 dv_cache_0003 p0003
  have p0005 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfCo x z y C A
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
      dv_cache_0010 dv_cache_0011 dv_cache_0012
  have p0006 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfCo x z y C B
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0013 dv_cache_0014 dv_cache_0015
      dv_cache_0010 dv_cache_0011 dv_cache_0012
  have p0007 :=
    @gN3sstr4g (synWss A B)
      (synCopab x z
        (synWex y (synWa (synWbr (.cv x) A (.cv y)) (synWbr (.cv y) C (.cv z)))))
      (synCopab x z
        (synWex y (synWa (synWbr (.cv x) B (.cv y)) (synWbr (.cv y) C (.cv z)))))
      (synCcom C A) (synCcom C B) p0004 p0005 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_coeq1`. -/
@[expose]
noncomputable def gCoeq1 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (synCcom A C) (synCcom B C))) :=
  by
  have p0000 := @gCoss1 A B C
  have p0001 := @gCoss1 B A C
  have p0002 :=
    @gAnim12i (synWss A B) (synWss (synCcom A C) (synCcom B C)) (synWss B A)
      (synWss (synCcom B C) (synCcom A C)) p0000 p0001
  have p0003 := @gEqss A B
  have p0004 := @gEqss (synCcom A C) (synCcom B C)
  have p0005 :=
    @gN3imtr4i (synWa (synWss A B) (synWss B A))
      (synWa (synWss (synCcom A C) (synCcom B C)) (synWss (synCcom B C) (synCcom A C)))
      (.classEq A B) (.classEq (synCcom A C) (synCcom B C)) p0002 p0003 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_coeq2`. -/
@[expose]
noncomputable def gCoeq2 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (synCcom C A) (synCcom C B))) :=
  by
  have p0000 := @gCoss2 A B C
  have p0001 := @gCoss2 B A C
  have p0002 :=
    @gAnim12i (synWss A B) (synWss (synCcom C A) (synCcom C B)) (synWss B A)
      (synWss (synCcom C B) (synCcom C A)) p0000 p0001
  have p0003 := @gEqss A B
  have p0004 := @gEqss (synCcom C A) (synCcom C B)
  have p0005 :=
    @gN3imtr4i (synWa (synWss A B) (synWss B A))
      (synWa (synWss (synCcom C A) (synCcom C B)) (synWss (synCcom C B) (synCcom C A)))
      (.classEq A B) (.classEq (synCcom C A) (synCcom C B)) p0002 p0003 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_coeq1i`. -/
@[expose]
noncomputable def gCoeq1i (A : Class) (B : Class) (C : Class)
    (hyp_coeq1i_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (.classEq (synCcom A C) (synCcom B C)) :=
  by
  have p0000 := @gCoeq1 A B C
  have p0001 := Nominal.mp hyp_coeq1i_1 p0000
  exact p0001


end NFChoice.DirectNominalPrf.WPPReplay

end
